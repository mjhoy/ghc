{-# LANGUAGE CPP #-}

module Exitify ( exitifyProgram ) where

#include "HsVersions.h"

import Var
import Id
import IdInfo
import CoreSyn
import CoreUtils
import Util
import State
import Unique
import VarSet
import VarEnv
import CoreFVs
import Outputable
import FastString

import Data.Bifunctor
import Control.Monad

-- | Traverses the AST, simply to find all joinrecs and call 'exitify' on them.
exitifyProgram :: CoreProgram -> CoreProgram
exitifyProgram binds = map goTopLvl binds
  where
    goTopLvl (NonRec v e) = NonRec v (go in_scope_toplvl e)
    goTopLvl (Rec pairs) = Rec (map (second (go in_scope_toplvl)) pairs)

    in_scope_toplvl = emptyInScopeSet `extendInScopeSetList` bindersOfBinds binds

    go :: InScopeSet -> CoreExpr -> CoreExpr
    go _ e@(Var{})       = e
    go _ e@(Lit {})      = e
    go _ e@(Type {})     = e
    go _ e@(Coercion {}) = e

    go in_scope (Lam v e')  = Lam v (go in_scope' e')
      where in_scope' = in_scope `extendInScopeSet` v
    go in_scope (App e1 e2) = App (go in_scope e1) (go in_scope e2)
    go in_scope (Case scrut bndr ty alts)
        = Case (go in_scope scrut) bndr ty (map (goAlt in_scope') alts)
      where in_scope' = in_scope `extendInScopeSet` bndr
    go in_scope (Cast e' c) = Cast (go in_scope e') c
    go in_scope (Tick t e') = Tick t (go in_scope e')
    go in_scope (Let bind body) = goBind in_scope bind (go in_scope' body)
      where in_scope' = in_scope `extendInScopeSetList` bindersOf bind

    goAlt :: InScopeSet -> CoreAlt -> CoreAlt
    goAlt in_scope (dc, pats, rhs) = (dc, pats, go in_scope' rhs)
      where in_scope' = in_scope `extendInScopeSetList` pats

    goBind :: InScopeSet -> CoreBind -> (CoreExpr -> CoreExpr)
    goBind in_scope (NonRec v rhs) = Let (NonRec v (go in_scope rhs))
    goBind in_scope (Rec pairs)
        | is_join_rec = exitify in_scope' pairs'
        | otherwise   = Let (Rec pairs')
      where pairs' = map (second (go in_scope')) pairs
            is_join_rec = any (isJoinId . fst) pairs
            in_scope' = in_scope `extendInScopeSetList` bindersOf (Rec pairs)

-- | Given a recursive group of a joinrec, identifies “exit paths” and binds them as
-- join-points outside the joinrec.
exitify :: InScopeSet -> [(Var,CoreExpr)] -> (CoreExpr -> CoreExpr)
exitify in_scope pairs =
    ASSERT (all (isJoinId . fst) pairs)
    \body ->mkExitLets exits (mkLetRec pairs' body)
  where
    mkExitLets ((exitId, exitRhs):exits') = mkLetNonRec exitId exitRhs . mkExitLets exits'
    mkExitLets [] = id

    -- We need the set of free variables of many subexpressions here, so
    -- annotate the AST with them
    ann_pairs = map (second freeVars) pairs

    -- Which are the recursive calls?
    recursive_calls = mkVarSet $ map fst pairs

    (pairs',exits) = (`runState` []) $ do
        forM ann_pairs $ \(x,rhs) -> do
            -- go past the lambdas of the join point
            let (args, body) = collectNAnnBndrs (idJoinArity x) rhs
            body' <- go args body
            let rhs' = mkLams args body'
            return (x, rhs')

    -- main working function. Goes through the RHS (tail-call positions only),
    -- checks if there are no more recursive calls, if so, abstracts over
    -- variables bound on the way and lifts it out as a join point.
    --
    -- It uses a state monad to keep track of floated binds

    go :: [Var]           -- ^ variables to abstract over
       -> CoreExprWithFVs -- ^ current expression in tail position
       -> State [(Id, CoreExpr)] CoreExpr

    go captured ann_e
        -- Do not touch an expression that is already a join call with no free variables
        -- in the arguments
        | (Var f, args) <- collectArgs e
        , isJoinId f
        , isEmptyVarSet (exprsFreeVars args `minusVarSet` mkVarSet captured)
        = return e

        -- Do not touch a boring expression
        | is_exit, not is_interesting = return e

        -- We have something to float out!
        | is_exit = do
            -- Assemble the RHS of the exit join point
            let args = filter (`elemVarSet` fvs) captured
                rhs = mkLams args e
                ty = exprType rhs
            -- Pick a suitable name
            v <- mkExitJoinId ty (length args) captured
            -- Remember this binding
            addExit v rhs
            -- And call it from here
            return $ mkVarApps (Var v) args
      where
        -- An exit expression has no recursive calls
        is_exit = disjointVarSet fvs recursive_calls
        -- An interesting exit expression has free variables from
        -- outside the recursive group
        is_interesting = not (isEmptyVarSet (fvs `minusVarSet` mkVarSet captured))

        e = deAnnotate ann_e
        fvs = dVarSetToVarSet (freeVarsOf ann_e)


    go captured (_, AnnCase scrut bndr ty alts) = do
        alts' <- forM alts $ \(dc, pats, rhs) -> do
            rhs' <- go (pats ++ bndr : captured) rhs
            return (dc, pats, rhs')
        return $ Case (deAnnotate scrut) bndr ty alts'

    go _ ann_e = return (deAnnotate ann_e) -- TODO: What else is a tail-call position?


    -- Picks a new unique, which is disjoint from
    --  * the free variables of the whole joinrec
    --  * any bound variables (captured)
    --  * any exit join points created so far.
    mkExitJoinId ty join_arity captured = do
        fs <- get
        let avoid = in_scope `extendInScopeSetList` captured
                             `extendInScopeSetList` (map fst fs)
                             `extendInScopeSet` exit_id_tmpl -- just cosmetics
        return (uniqAway avoid exit_id_tmpl)
      where
        exit_id_tmpl = mkSysLocal (fsLit "exit") initExitJoinUnique ty
                        `asJoinId` join_arity
                        `setIdOccInfo` exit_occ_info

        exit_occ_info =
            OneOcc { occ_in_lam = True
                   , occ_one_br = True
                   , occ_int_cxt = False
                   , occ_tail = AlwaysTailCalled join_arity }

    addExit v rhs = do
        fs <- get
        put ((v,rhs):fs)


