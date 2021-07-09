{- |
Module      : Kore.Step.Simplification.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.In (
    simplify,
) where

import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.And as And
import qualified Kore.Step.Simplification.Ceil as Ceil (
    makeEvaluate,
    simplifyEvaluated,
 )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
import qualified Logic
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
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    In sort (OrPattern RewritingVariableName) ->
    simplifier (OrCondition RewritingVariableName)
simplify
    sideCondition
    In{inContainedChild = first, inContainingChild = second} =
        simplifyEvaluatedIn sideCondition first second

simplifyEvaluatedIn ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
simplifyEvaluatedIn sideCondition first second
    | OrPattern.isFalse first = return OrCondition.bottom
    | OrPattern.isFalse second = return OrCondition.bottom
    | OrPattern.isTrue first = Ceil.simplifyEvaluated sideCondition second
    | OrPattern.isTrue second = Ceil.simplifyEvaluated sideCondition first
    | otherwise =
        OrPattern.observeAllT $ do
            pattFirst <- Logic.scatter first
            pattSecond <- Logic.scatter second
            makeEvaluateIn sideCondition pattFirst pattSecond >>= Logic.scatter

makeEvaluateIn ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluateIn sideCondition first second
    | Pattern.isTop first = Ceil.makeEvaluate sideCondition second
    | Pattern.isTop second = Ceil.makeEvaluate sideCondition first
    | Pattern.isBottom first || Pattern.isBottom second = return OrCondition.bottom
    | otherwise =
        And.makeEvaluate
            Not.notSimplifier
            sideCondition
            (MultiAnd.make [first, second])
            & OrPattern.observeAllT
            >>= Ceil.simplifyEvaluated sideCondition
