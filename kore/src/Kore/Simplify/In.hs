{- |
Module      : Kore.Simplify.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.In (
    simplify,
) where

import Kore.Internal.Conditional qualified as Condition
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify
import Kore.Unification.Procedure (runUnifier, unificationProcedure)
import Logic qualified
import Prelude.Kore

{- |'simplify' simplifies an 'In' pattern with 'OrPattern'
children.

Right now this uses the following simplifications:

* bottom in a = bottom
* a in bottom = bottom
* top in a = ceil(a)
* a in top = ceil(a)

TODO(virgil): It does not have yet a special case for children with top terms.
-}
simplify ::
    SideCondition RewritingVariableName ->
    In sort (OrPattern RewritingVariableName) ->
    Simplifier (OrCondition RewritingVariableName)
simplify
    sideCondition
    In{inContainedChild = first, inContainingChild = second} =
        simplifyEvaluatedIn sideCondition first second

simplifyEvaluatedIn ::
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    Simplifier (OrCondition RewritingVariableName)
simplifyEvaluatedIn sideCondition first second =
    OrPattern.observeAllT $ do
        pattFirst <- Logic.scatter first
        pattSecond <- Logic.scatter second
        let termFirst = Pattern.term pattFirst
            termSecond = Pattern.term pattSecond
            condFirst = Pattern.withoutTerm pattFirst
            condSecond = Pattern.withoutTerm pattSecond
        unify termFirst termSecond
            <&> Condition.andCondition (condFirst <> condSecond)
  where
    unify ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        Logic.LogicT Simplifier (Condition RewritingVariableName)
    unify t1 t2 = do
        results <- lift $ runUnifier (unificationProcedure sideCondition t1 t2)
        Logic.scatter results
