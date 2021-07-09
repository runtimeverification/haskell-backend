{- |
Module      : Kore.Step.Simplification.Forall
Description : Tools for Forall pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Forall (
    simplify,
    makeEvaluate,
) where

import qualified Kore.Internal.Condition as Condition (
    fromPredicate,
    hasFreeVariable,
    markPredicateSimplified,
    toPredicate,
 )
import qualified Kore.Internal.Conditional as Conditional (
    withCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
    bottom,
    fromTermLike,
    isBottom,
    isTop,
    splitTerm,
    toTermLike,
    top,
 )
import Kore.Internal.Predicate (
    makeForallPredicate,
 )
import Kore.Internal.TermLike (
    ElementVariable,
    Forall (Forall),
    Sort,
    Variable (..),
    mkForall,
    mkSomeVariable,
 )
import qualified Kore.Internal.TermLike as TermLike (
    hasFreeVariable,
    markSimplified,
 )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Prelude.Kore

-- TODO: Move Forall up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.

{- |'simplify' simplifies an 'Forall' pattern with an 'OrPattern'
child.

Right now this has special cases for (top and bottom children),
(top and bottom term) and (top and bottom predicate-substitution).

Note that while forall x . phi(x) and [x=alpha] can be simplified
(it's bottom if x's sort is multivalued and alpha is not the 'x' pattern or
the identity function applied to the pattern x, or phi(alpha) otherwise),
we only expect forall usage for symbolic variables, so we won't attempt to
simplify it this way.
-}
simplify ::
    Forall Sort RewritingVariableName (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify Forall{forallVariable, forallChild} =
    simplifyEvaluated forallVariable forallChild

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Forall Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of a 'variable' and an 'OrPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Attribute.Pattern' annotation
will eventually cache information besides the pattern sort, which will make it
even more useful to carry around.

-}
simplifyEvaluated ::
    ElementVariable RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
simplifyEvaluated variable simplified
    | OrPattern.isTrue simplified = simplified
    | OrPattern.isFalse simplified = simplified
    | otherwise =
        OrPattern.map (makeEvaluate variable) simplified

{- | evaluates an 'Forall' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate ::
    ElementVariable RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName
makeEvaluate variable patt
    | Pattern.isTop patt = Pattern.top
    | Pattern.isBottom patt = Pattern.bottom
    | not variableInTerm && not variableInCondition = patt
    | predicateIsBoolean =
        TermLike.markSimplified (mkForall variable term)
            `Conditional.withCondition` predicate
    | termIsBoolean =
        term
            `Conditional.withCondition` Condition.markPredicateSimplified
                ( Condition.fromPredicate
                    (makeForallPredicate variable (Condition.toPredicate predicate))
                )
    | otherwise =
        Pattern.fromTermLike $
            TermLike.markSimplified $
                mkForall variable $
                    Pattern.toTermLike patt
  where
    (term, predicate) = Pattern.splitTerm patt
    someVariable = mkSomeVariable variable
    someVariableName = variableName someVariable
    variableInTerm = TermLike.hasFreeVariable someVariableName term
    variableInCondition = Condition.hasFreeVariable someVariableName predicate
    termIsBoolean = isTop term || isBottom term
    predicateIsBoolean = isTop predicate || isBottom predicate
