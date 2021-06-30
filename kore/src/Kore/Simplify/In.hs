{- |
Module      : Kore.Simplify.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.In (
    simplify,
) where

import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.And as And
import qualified Kore.Simplify.Ceil as Ceil (
    makeEvaluate,
    simplifyEvaluated,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Simplify.Simplify
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
    In Sort (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify
    sideCondition
    In{inContainedChild = first, inContainingChild = second} =
        simplifyEvaluatedIn sideCondition first second

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make
'simplifyEvaluatedIn' take an argument of type

> CofreeF (In Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluateIn' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluatedIn ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyEvaluatedIn sideCondition first second
    | OrPattern.isFalse first = return OrPattern.bottom
    | OrPattern.isFalse second = return OrPattern.bottom
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
    simplifier (OrPattern RewritingVariableName)
makeEvaluateIn sideCondition first second
    | Pattern.isTop first = Ceil.makeEvaluate sideCondition second
    | Pattern.isTop second = Ceil.makeEvaluate sideCondition first
    | Pattern.isBottom first || Pattern.isBottom second = return OrPattern.bottom
    | otherwise =
        And.makeEvaluate
            Not.notSimplifier
            sideCondition
            (MultiAnd.make [first, second])
            & OrPattern.observeAllT
            >>= Ceil.simplifyEvaluated sideCondition
