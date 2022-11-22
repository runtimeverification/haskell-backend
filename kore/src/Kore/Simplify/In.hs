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

import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.NormalForm qualified as NormalForm
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrCondition qualified as OrCondition
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
import Kore.Simplify.And qualified as And
import Kore.Simplify.Ceil qualified as Ceil (
    makeEvaluate,
    simplifyEvaluated,
 )
import Kore.Simplify.Not qualified as Not
import Kore.Simplify.Simplify
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
simplifyEvaluatedIn sideCondition first second
    | OrPattern.isFalse first = return OrCondition.bottom
    | OrPattern.isFalse second = return OrCondition.bottom
    | OrPattern.isTrue first =
        NormalForm.toOrCondition <$> Ceil.simplifyEvaluated sideCondition second
    | OrPattern.isTrue second =
        NormalForm.toOrCondition <$> Ceil.simplifyEvaluated sideCondition first
    | otherwise =
        OrPattern.observeAllT $ do
            pattFirst <- Logic.scatter first
            pattSecond <- Logic.scatter second
            makeEvaluateIn sideCondition pattFirst pattSecond >>= Logic.scatter

makeEvaluateIn ::
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    Logic.LogicT Simplifier (OrCondition RewritingVariableName)
makeEvaluateIn sideCondition first second
    | Pattern.isTop first =
        NormalForm.toOrCondition <$> Ceil.makeEvaluate sideCondition second
    | Pattern.isTop second =
        NormalForm.toOrCondition <$> Ceil.makeEvaluate sideCondition first
    | Pattern.isBottom first || Pattern.isBottom second = return OrCondition.bottom
    | otherwise =
        (And.makeEvaluate pattSort Not.notSimplifier sideCondition)
            (MultiAnd.make [first, second])
            & OrPattern.observeAllT
            >>= Ceil.simplifyEvaluated sideCondition
            <&> NormalForm.toOrCondition
  where
    pattSort = patternSort first
