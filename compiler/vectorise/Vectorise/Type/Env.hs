-- Vectorise a modules type and class declarations.
--
-- This produces new type constructors and family instances top be included in the module toplevel
-- as well as bindings for worker functions, dfuns, and the like.

module Vectorise.Type.Env ( 
  vectTypeEnv,
) where
  
#include "HsVersions.h"

import Vectorise.Env
import Vectorise.Vect
import Vectorise.Monad
import Vectorise.Builtins
import Vectorise.Type.TyConDecl
import Vectorise.Type.Classify
import Vectorise.Generic.PADict
import Vectorise.Generic.PAMethods
import Vectorise.Generic.PData
import Vectorise.Generic.Description
import Vectorise.Utils

import CoreSyn
import CoreUtils
import CoreUnfold
import DataCon
import TyCon
import Type
import FamInstEnv
import Id
import MkId
import NameEnv
import NameSet

import Util
import Outputable
import FastString
import MonadUtils
import Control.Monad
import Data.List

-- Note [Pragmas to vectorise tycons]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- VECTORISE pragmas for type constructors cover three different flavours of vectorising data type
-- constructors:
--
-- (1) Data type constructor 'T' that may be used in vectorised code, where 'T' represents itself,
--     but the representation of 'T' is opaque in vectorised code.  
--
--     An example is the treatment of 'Int'.  'Int's can be used in vectorised code and remain
--     unchanged by vectorisation.  However, the representation of 'Int' by the 'I#' data
--     constructor wrapping an 'Int#' is not exposed in vectorised code.  Instead, computations
--     involving the representation need to be confined to scalar code.
--
--     'PData' and 'PRepr' instances need to be explicitly supplied for 'T' (they are not generated
--     by the vectoriser).
--
--     Type constructors declared with {-# VECTORISE SCALAR type T #-} are treated in this manner.
--     (The vectoriser never treats a type constructor automatically in this manner.)
--
-- (2) Data type constructor 'T' that together with its constructors 'Cn' may be used in vectorised
--     code, where 'T' and the 'Cn' are automatically vectorised in the same manner as data types
--     declared in a vectorised module.  This includes the case where the vectoriser determines that
--     the original representation of 'T' may be used in vectorised code (as it does not embed any
--     parallel arrays.)  This case is for type constructors that are *imported* from a non-
--     vectorised module, but that we want to use with full vectorisation support.
--
--     An example is the treatment of 'Ordering' and '[]'.  The former remains unchanged by
--     vectorisation, whereas the latter is fully vectorised.

--     'PData' and 'PRepr' instances are automatically generated by the vectoriser.
--
--     Type constructors declared with {-# VECTORISE type T #-} are treated in this manner.
--
-- (3) Data type constructor 'T' that together with its constructors 'Cn' may be used in vectorised
--     code, where 'T' is represented by an explicitly given 'Tv' whose constructors 'Cvn' represent
--     the original constructors in vectorised code.  As a special case, we can have 'Tv = T'
--
--     An example is the treatment of 'Bool', which is represented by itself in vectorised code
--     (as it cannot embed any parallel arrays).  However, we do not want any automatic generation
--     of class and family instances, which is why Case (2) does not apply.
--
--     'PData' and 'PRepr' instances need to be explicitly supplied for 'T' (they are not generated
--     by the vectoriser).
--
--     Type constructors declared with {-# VECTORISE type T = T' #-} are treated in this manner.
--
-- In addition, we have also got a single pragma form for type classes: {-# VECTORISE class C #-}.
-- It implies that the class type constructor may be used in vectorised code together with its data
-- constructor.  We generally produce a vectorised version of the data type and data constructor.
-- We do not generate 'PData' and 'PRepr' instances for class type constructors.  This pragma is the
-- default for all type classes declared in this module, but the pragma can also be used explitly on
-- imported classes.

-- Note [Vectorising classes]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We vectorise classes essentially by just vectorising their desugared Core representation, but we
-- do generate a 'Class' structure along the way (see 'Vectorise.Type.TyConDecl.vectTyConDecl').
--
-- Here is an example illustrating the mapping — assume
--
--   class Num a where
--     (+) :: a -> a -> a
--
-- It desugars to
--
--   data Num a = D:Num { (+) :: a -> a -> a }
--
-- which we vectorise to
--
--  data V:Num a = D:V:Num { ($v+) :: PArray a :-> PArray a :-> PArray a }
--
-- while adding the following entries to the vectorisation map:
--
--   tycon  : Num   --> V:Num
--   datacon: D:Num --> D:V:Num
--   var    : (+) --> ($v+)

-- |Vectorise type constructor including class type constructors.
--
vectTypeEnv :: [TyCon]                  -- Type constructors defined in this module
            -> [CoreVect]               -- All 'VECTORISE [SCALAR] type' declarations in this module
            -> [CoreVect]               -- All 'VECTORISE class' declarations in this module
            -> VM ( [TyCon]             -- old TyCons ++ new TyCons
                  , [FamInst]           -- New type family instances.
                  , [(Var, CoreExpr)])  -- New top level bindings.
vectTypeEnv tycons vectTypeDecls vectClassDecls
  = do { traceVt "** vectTypeEnv" $ ppr tycons

         -- Build a map containing all vectorised type constructor.  If they are scalar, they are
         -- mapped to 'False' (vectorised type constructor == original type constructor).
       ; allScalarTyConNames <- globalScalarTyCons  -- covers both current and imported modules
       ; vectTyCons          <- globalVectTyCons
       ; let vectTyConBase    = mapNameEnv (const True) vectTyCons   -- by default fully vectorised
             vectTyConFlavour = foldNameSet (\n env -> extendNameEnv env n False) vectTyConBase
                                            allScalarTyConNames

       ; let   -- {-# VECTORISE SCALAR type T -#} (imported and local tycons)
             localScalarTyCons      = [tycon | VectType True  tycon Nothing <- vectTypeDecls]

               -- {-# VECTORISE type T -#} (ONLY the imported tycons)
             impVectTyCons          = (   [tycon | VectType False tycon Nothing <- vectTypeDecls]
                                       ++ [tycon | VectClass tycon              <- vectClassDecls])
                                      \\ tycons

               -- {-# VECTORISE type T = ty -#} (imported and local tycons)
             vectTyConsWithRHS      = [ (tycon, rhs) 
                                      | VectType False tycon (Just rhs) <- vectTypeDecls]

               -- filter VECTORISE SCALAR tycons and VECTORISE tycons with explicit rhses
             vectSpecialTyConNames  = mkNameSet . map tyConName $
                                        localScalarTyCons ++ map fst vectTyConsWithRHS
             notLocalScalarTyCon tc = not $ (tyConName tc) `elemNameSet` vectSpecialTyConNames

           -- Split the list of 'TyCons' into the ones (1) that we must vectorise and those (2)
           -- that we could, but don't need to vectorise.  Type constructors that are not data
           -- type constructors or use non-Haskell98 features are being dropped.  They may not
           -- appear in vectorised code.  (We also drop the local type constructors appearing in a
           -- VECTORISE SCALAR pragma or a VECTORISE pragma with an explicit right-hand side, as
           -- these are being handled separately.)
           -- Furthermore, 'drop_tcs' are those type constructors that we cannot vectorise.
       ; let maybeVectoriseTyCons           = filter notLocalScalarTyCon tycons ++ impVectTyCons
             (conv_tcs, keep_tcs, drop_tcs) = classifyTyCons vectTyConFlavour maybeVectoriseTyCons
             orig_tcs                       = keep_tcs ++ conv_tcs
             
       ; traceVt " VECT SCALAR    : " $ ppr localScalarTyCons
       ; traceVt " VECT [class]   : " $ ppr impVectTyCons
       ; traceVt " VECT with rhs  : " $ ppr (map fst vectTyConsWithRHS)
       ; traceVt " -- after classification (local and VECT [class] tycons) --" empty
       ; traceVt " reuse          : " $ ppr keep_tcs
       ; traceVt " convert        : " $ ppr conv_tcs
       
           -- warn the user about unvectorised type constructors
       ; let explanation = ptext (sLit "(They use unsupported language extensions") $$
                           ptext (sLit "or depend on type constructors that are not vectorised)")
       ; unless (null drop_tcs) $
           emitVt "Warning: cannot vectorise these type constructors:" $ 
             pprQuotedList drop_tcs $$ explanation

       ; let defTyConDataCons origTyCon vectTyCon
               = do { defTyCon origTyCon vectTyCon
                    ; MASSERT(length (tyConDataCons origTyCon) == length (tyConDataCons vectTyCon))
                    ; zipWithM_ defDataCon (tyConDataCons origTyCon) (tyConDataCons vectTyCon)
                    }

           -- For the type constructors that we don't need to vectorise, we use the original
           -- representation in both unvectorised and vectorised code.
       ; zipWithM_ defTyConDataCons keep_tcs keep_tcs

           -- We do the same for type constructors declared VECTORISE SCALAR, while ignoring their
           -- representation (data constructors) — see "Note [Pragmas to vectorise tycons]".
       ; zipWithM_ defTyCon localScalarTyCons localScalarTyCons

           -- For type constructors declared VECTORISE with an explicit vectorised type, we use the
           -- explicitly given type in vectorised code and map data constructors one for one — see
           -- "Note [Pragmas to vectorise tycons]".
       ; mapM_ (uncurry defTyConDataCons) vectTyConsWithRHS

           -- Vectorise all the data type declarations that we can and must vectorise (enter the
           -- type and data constructors into the vectorisation map on-the-fly.)
       ; new_tcs <- vectTyConDecls conv_tcs

           -- We don't need new representation types for dictionary constructors. The constructors
           -- are always fully applied, and we don't need to lift them to arrays as a dictionary
           -- of a particular type always has the same value.
       ; let vect_tcs = filter (not . isClassTyCon) 
                      $ keep_tcs ++ new_tcs

           -- Build 'PRepr' and 'PData' instance type constructors and family instances for all
           -- type constructors with vectorised representations.
       ; reprs      <- mapM tyConRepr vect_tcs
       ; repr_tcs   <- zipWith3M buildPReprTyCon  orig_tcs vect_tcs reprs
       ; pdata_tcs  <- zipWith3M buildPDataTyCon  orig_tcs vect_tcs reprs
       ; pdatas_tcs <- zipWith3M buildPDatasTyCon orig_tcs vect_tcs reprs

       ; let inst_tcs  = repr_tcs ++ pdata_tcs ++ pdatas_tcs
             fam_insts = map mkLocalFamInst inst_tcs
       ; updGEnv $ extendFamEnv fam_insts

           -- Generate dfuns for the 'PA' instances of the vectorised type constructors and
           -- associate the type constructors with their dfuns in the global environment.  We get
           -- back the dfun bindings (which we will subsequently inject into the modules toplevel).
       ; (_, binds) <- fixV $ \ ~(dfuns, _) ->
           do { defTyConPAs (zipLazy vect_tcs dfuns)
              ; dfuns <- sequence 
                      $  zipWith5 buildTyConBindings
                                  orig_tcs
                                  vect_tcs
                                  repr_tcs
                                  pdata_tcs
                                  pdatas_tcs

              ; binds <- takeHoisted
              ; return (dfuns, binds)
              }

           -- Return the vectorised variants of type constructors as well as the generated instance
           -- type constructors, family instances, and dfun bindings.
       ; return (new_tcs ++ inst_tcs, fam_insts, binds)
       }


-- Helpers --------------------------------------------------------------------
buildTyConBindings :: TyCon -> TyCon -> TyCon -> TyCon -> TyCon -> VM Var
buildTyConBindings orig_tc vect_tc prepr_tc pdata_tc pdatas_tc
 = do   vectDataConWorkers orig_tc vect_tc pdata_tc
        repr <- tyConRepr vect_tc
        buildPADict vect_tc prepr_tc pdata_tc pdatas_tc repr
      

vectDataConWorkers :: TyCon -> TyCon -> TyCon -> VM ()
vectDataConWorkers orig_tc vect_tc arr_tc
 = do bs <- sequence
          . zipWith3 def_worker  (tyConDataCons orig_tc) rep_tys
          $ zipWith4 mk_data_con (tyConDataCons vect_tc)
                                 rep_tys
                                 (inits rep_tys)
                                 (tail $ tails rep_tys)
      mapM_ (uncurry hoistBinding) bs
 where
    tyvars   = tyConTyVars vect_tc
    var_tys  = mkTyVarTys tyvars
    ty_args  = map Type var_tys
    res_ty   = mkTyConApp vect_tc var_tys

    cons     = tyConDataCons vect_tc
    arity    = length cons
    [arr_dc] = tyConDataCons arr_tc

    rep_tys  = map dataConRepArgTys $ tyConDataCons vect_tc


    mk_data_con con tys pre post
      = liftM2 (,) (vect_data_con con)
                   (lift_data_con tys pre post (mkDataConTag con))

    sel_replicate len tag
      | arity > 1 = do
                      rep <- builtin (selReplicate arity)
                      return [rep `mkApps` [len, tag]]

      | otherwise = return []

    vect_data_con con = return $ mkConApp con ty_args
    lift_data_con tys pre_tys post_tys tag
      = do
          len  <- builtin liftingContext
          args <- mapM (newLocalVar (fsLit "xs"))
                  =<< mapM mkPDataType tys

          sel  <- sel_replicate (Var len) tag

          pre   <- mapM emptyPD (concat pre_tys)
          post  <- mapM emptyPD (concat post_tys)

          return . mkLams (len : args)
                 . wrapFamInstBody arr_tc var_tys
                 . mkConApp arr_dc
                 $ ty_args ++ sel ++ pre ++ map Var args ++ post

    def_worker data_con arg_tys mk_body
      = do
          arity <- polyArity tyvars
          body <- closedV
                . inBind orig_worker
                . polyAbstract tyvars $ \args ->
                  liftM (mkLams (tyvars ++ args) . vectorised)
                $ buildClosures tyvars [] arg_tys res_ty mk_body

          raw_worker <- mkVectId orig_worker (exprType body)
          let vect_worker = raw_worker `setIdUnfolding`
                              mkInlineUnfolding (Just arity) body
          defGlobalVar orig_worker vect_worker
          return (vect_worker, body)
      where
        orig_worker = dataConWorkId data_con
