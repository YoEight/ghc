--
-- Copyright (c) 2014 Joachim Breitner
--

module CallArity
    ( callArityAnalProgram
    ) where

import VarSet
import VarEnv
import DynFlags ( DynFlags )

import BasicTypes
import CoreSyn
import Id
import CoreArity

import Control.Arrow ( second )
import Data.Maybe ( fromMaybe, isJust )



{-
%************************************************************************
%*									*
              Call Arity Analyis
%*									*
%************************************************************************


For let-bound things, find out the minimum arity it is called with, so that the
value can be eta-expanded to that arity, creating better code (main goal: good
foldl as foldr).

Main problem: Thunks! We must not lose sharing. So one needs to consider how
often something is called. We use the following approximation:

    Only consider tail calls!

This allows us to detect that there is at most one call to n in

 let n = case .. of .. -- A thunk!
 in case .. of
     True -> let go = \y -> case .. of
                              True -> go (y+1)
                              False > n
    False -> n

despite a call from a recursive function, becuase

    A tail-recursive function can make at most one tail-call somewhere else.


The following code is not yet very quick. Possible improvements:
 * Re-use existing information in nested fixed-points.
 * Upon failure in fixed-pointing, go directly to 0 (or the manifestArity).

Possibe improvements in precision:
 * Always start with at least the manifestArity.
 * When analysing a recursive RHS, starting with its manifestArity,
   even if it calls itself at a lower arity, that is still good enough to stop.
 * In the above, use exprArity instead of manifestArity.

-}

callArityAnalProgram :: DynFlags -> CoreProgram -> CoreProgram
callArityAnalProgram _dflags = map callArityBind

callArityBind :: CoreBind -> CoreBind
callArityBind (NonRec id rhs) = NonRec id (callArityRHS rhs) 
callArityBind (Rec binds) = Rec $ map (\(id,rhs) -> (id, callArityRHS rhs)) binds

callArityRHS :: CoreExpr -> CoreExpr
callArityRHS = snd . callArityAnal 0 emptyVarSet


type CallArityEnv = VarEnv (Maybe Arity)

callArityAnal ::
    Arity ->  -- The arity this expression is called with
    VarSet -> -- The set of interesting variables
    CoreExpr ->  -- The expression to analyse
    (CallArityEnv, CoreExpr)
        -- How this expression uses its interesting variables:
        --   Just n  => a tail call with that arity
        --   Nothing => other uses
        -- and the expression with IdInfo updated

-- The trivial base cases
callArityAnal _     _   e@(Lit _)
    = (emptyVarEnv, e)
callArityAnal _     _   e@(Type _)
    = (emptyVarEnv, e)
callArityAnal _     _   e@(Coercion _)
    = (emptyVarEnv, e)
-- The transparent cases
callArityAnal arity int (Tick t e)
    = second (Tick t) $ callArityAnal arity int e
callArityAnal arity int (Cast e co)
    = second (\e -> Cast e co) $ callArityAnal arity int e

-- The interesting case: Variables, Lambdas, Lets, Applications, Cases
callArityAnal arity int e@(Var v)
    | v `elemVarSet` int
    = (unitVarEnv v (Just arity), e)
    | otherwise
    = (emptyVarEnv, e)

-- We have a lambda that we are not sure to call. Tail calls therein
-- are no longer tail calls
callArityAnal 0     int (Lam v e)
    = (ae', Lam v e')
  where
    (ae, e') = callArityAnal 0 int e
    ae' = forgetTailCalls ae
-- We have a lambda that we are calling. decrease arity.
callArityAnal arity int (Lam v e)
    = (ae, Lam v e')
  where
    (ae, e') = callArityAnal (arity - 1) int e

-- Boring non-recursive let, i.e. no eta expansion possible. do not be smart about this
callArityAnal arity int (Let (NonRec v rhs) e)
    | exprArity rhs >= length (typeArity (idType v))
    = (ae_final, Let (NonRec v rhs') e')
  where
    (ae_rhs, rhs') = callArityAnal 0 int rhs
    (ae_body, e')  = callArityAnal arity int e
    ae_final = forgetTailCalls ae_rhs `lubEnv` ae_body

-- Non-recursive let. Find out how the body calls the rhs, analise that,
-- and combine the results, convervatively using both
callArityAnal arity int (Let (NonRec v rhs) e)

    -- We are tail-calling into the rhs. So a tail-call in the RHS is a
    -- tail-call for everything
    | Just n <- rhs_arity
    = let (ae_rhs, rhs') = callArityAnal n int rhs
          final_ae       = ae_rhs `lubEnv` ae_body'
          v'             = v `setIdCallArity` n
      in -- pprTrace "callArityAnal:LetNonRecTailCall"
         --          (vcat [ppr v, ppr arity, ppr n, ppr final_ae ])
         (final_ae, Let (NonRec v' rhs') e')

    -- We are calling the rhs in any other way (or not at all), so kill the
    -- tail-call information from there
    | otherwise
    = let (ae_rhs, rhs') = callArityAnal 0 int rhs
          final_ae = forgetTailCalls ae_rhs `lubEnv` ae_body'
          v'             = v `setIdCallArity` 0
      in -- pprTrace "callArityAnal:LetNonRecNonTailCall"
         --          (vcat [ppr v, ppr arity, ppr final_ae ])
         (final_ae, Let (NonRec v' rhs') e')
  where
    int_body = int `extendVarSet` v
    (ae_body, e') = callArityAnal arity int_body e
    ae_body' = ae_body `delVarEnv` v
    rhs_arity = lookupWithDefaultVarEnv ae_body Nothing v

-- Boring recursive let, i.e. no eta expansion possible. do not be smart about this
callArityAnal arity int (Let (Rec [(v,rhs)]) e)
    | exprArity rhs >= length (typeArity (idType v))
    = (ae_final, Let (Rec [(v,rhs')]) e')
  where
    (ae_rhs, rhs') = callArityAnal 0 int rhs
    (ae_body, e')  = callArityAnal arity int e
    ae_final = forgetTailCalls ae_rhs `lubEnv` ae_body

-- Recursive let. Again, find out how the body calls the rhs, analise that,
-- but then check if it is compatible with how rhs calls itself. If not,
-- retry with lower arity.
callArityAnal arity int (Let (Rec [(v,rhs)]) e)
    -- We are tail-calling into the rhs. So a tail-call in the RHS is a
    -- tail-call for everything
    | Just n <- rhs_arity
    = let (ae_rhs, rhs_arity', rhs') = callArityFix n int_body v rhs
          final_ae = ae_rhs `lubEnv` ae_body'
          v'             = v `setIdCallArity` fromMaybe 0 rhs_arity'
      in -- pprTrace "callArityAnal:LetRecTailCall"
         --          (vcat [ppr v, ppr arity, ppr n, ppr rhs_arity', ppr final_ae ])
         (final_ae, Let (Rec [(v',rhs')]) e')
    -- We are calling the body in any other way (or not at all), so kill the
    -- tail-call information from there. No need to iterate there.
    | otherwise
    = let (ae_rhs, rhs') = callArityAnal 0 int_body rhs
          final_ae = forgetTailCalls ae_rhs `lubEnv` ae_body'
          v'             = v `setIdCallArity` 0
      in -- pprTrace "callArityAnal:LetRecNonTailCall"
         --          (vcat [ppr v, ppr arity, ppr final_ae ])
         (final_ae, Let (Rec [(v',rhs')]) e')
  where
    int_body = int `extendVarSet` v
    (ae_body, e') = callArityAnal arity int_body e
    ae_body' = ae_body `delVarEnv` v
    rhs_arity = lookupWithDefaultVarEnv ae_body Nothing v

-- Mutual recursion. Do nothing serious here, for now
callArityAnal arity int (Let (Rec binds) e)
    = (final_ae, Let (Rec binds') e')
  where
    (aes, binds') = unzip $ map go binds
    go (i,e) = let (ae,e') = callArityAnal 0 int e
               in (forgetTailCalls ae, (i,e'))
    (ae, e') = callArityAnal arity int e
    final_ae = foldl lubEnv ae aes

-- Application. Increase arity for the called expresion, nothing to know about
-- the second
callArityAnal arity int (App e1 e2)
    = (final_ae, App e1' e2')
  where
    (ae1, e1') = callArityAnal (arity + 1) int e1
    (ae2, e2') = callArityAnal 0           int e2
    final_ae = ae1 `useBetterOf` ae2

-- Case expression. Here we decide whether
-- we want to look at calls from the scrunitee or the alternatives;
-- one of them we set to Nothing.
-- Naive idea: If there are interesting calls in the scrunitee,
-- zap the alternatives
callArityAnal arity int (Case scrut bndr ty alts)
    = -- pprTrace "callArityAnal:Case"
      --          (vcat [ppr scrut, ppr final_ae])
      (final_ae, Case scrut' bndr ty alts')
  where
    (alt_aes, alts') = unzip $ map go alts
    go (dc, bndrs, e) = let (ae, e') = callArityAnal arity int e
                        in  (ae, (dc, bndrs, e'))
    alt_ae = foldl lubEnv emptyVarEnv alt_aes
    (scrut_ae, scrut') = callArityAnal 0 int scrut
    final_ae = scrut_ae `useBetterOf` alt_ae

callArityFix :: Arity -> VarSet -> Id -> CoreExpr -> (CallArityEnv, Maybe Arity, CoreExpr)
callArityFix arity int v e
    | Nothing <- new_arity
    -- Not tail recusive, rerun with arity 0 and bail out
    -- (Or not recursive at all, but that was hopefully handled by the simplifier before)
    = let (ae, e') = callArityAnal 0 int e
      in (forgetTailCalls ae `delVarEnv` v, Nothing, e')
    | Just n <- new_arity, n < arity
    -- Retry
    = callArityFix n int v e
    | otherwise
    -- RHS calls itself with at least as many arguments as the body of the let
    = (ae `delVarEnv` v, new_arity, e')
  where
    (ae, e') = callArityAnal arity int e
    new_arity = lookupWithDefaultVarEnv ae Nothing v


anyTailCalls :: VarEnv (Maybe Arity) -> Bool
anyTailCalls = foldVarEnv ((||) . isJust) False

forgetTailCalls :: VarEnv (Maybe Arity) -> VarEnv (Maybe Arity)
forgetTailCalls = mapVarEnv (const Nothing)

useBetterOf :: CallArityEnv -> CallArityEnv -> CallArityEnv
useBetterOf ae1 ae2 | anyTailCalls ae1 = ae1 `lubEnv` forgetTailCalls ae2
useBetterOf ae1 ae2 | otherwise        = forgetTailCalls ae1 `lubEnv` ae2

-- Used when combining results from alternative cases; take the minimum
lubEnv :: CallArityEnv -> CallArityEnv -> CallArityEnv
lubEnv = plusVarEnv_C min



