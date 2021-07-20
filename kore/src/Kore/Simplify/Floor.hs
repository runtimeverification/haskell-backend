{- |
Module      : Kore.Simplify.Floor
Description : Tools for Floor pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Floor (
    simplify,
    makeEvaluateFloor,
) where

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeFloorPredicate,
 )
import qualified Kore.Internal.Predicate as Predicate (
    markSimplified,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

{- | 'simplify' simplifies a 'Floor' of 'OrPattern'.

We also take into account that
* floor(top) = top
* floor(bottom) = bottom
* floor leaves predicates and substitutions unchanged
* floor transforms terms into predicates

However, we don't take into account things like
floor(a and b) = floor(a) and floor(b).
-}
simplify ::
    Floor Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify Floor{floorResultSort = resultSort, floorChild = child} =
    simplifyEvaluatedFloor resultSort child

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Floor Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluateFloor'
may be changed analogously. The 'Attribute.Pattern' annotation will eventually
cache information besides the pattern sort, which will make it even more useful
to carry around.

-}
simplifyEvaluatedFloor ::
    Sort ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
simplifyEvaluatedFloor resultSort child =
    case toList child of
        [childP] -> makeEvaluateFloor resultSort childP
        _ -> makeEvaluateFloor resultSort (OrPattern.toPattern resultSort child)

{- | 'makeEvaluateFloor' simplifies a 'Floor' of 'Pattern'.

See 'simplify' for details.
-}
makeEvaluateFloor ::
    Sort ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateFloor resultSort child
    | Pattern.isTop child = OrPattern.top resultSort
    | Pattern.isBottom child = OrPattern.bottom
    | otherwise = makeEvaluateNonBoolFloor resultSort child

makeEvaluateNonBoolFloor ::
    Sort ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateNonBoolFloor resultSort patt@Conditional{term = Top_ _} =
    OrPattern.fromPattern patt{term = mkTop resultSort} -- remove the term's sort
    -- TODO(virgil): Also evaluate functional patterns to bottom for non-singleton
    -- sorts, and maybe other cases also
makeEvaluateNonBoolFloor resultSort patt =
    floorCondition <> condition
        & (Pattern.fromCondition resultSort)
        & OrPattern.fromPattern
  where
    (term, condition) = Pattern.splitTerm patt
    floorCondition =
        makeFloorPredicate term
            & Predicate.markSimplified
            & Condition.fromPredicate
