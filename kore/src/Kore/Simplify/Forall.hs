{- |
Module      : Kore.Simplify.Forall
Description : Tools for Forall pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Forall (
    simplify,
    makeEvaluate,
) where

import Kore.Internal.Condition qualified as Condition (
    fromPredicate,
    hasFreeVariable,
    markPredicateSimplified,
    toPredicate,
 )
import Kore.Internal.Conditional qualified as Conditional (
    withCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern (
    bottomOf,
    fromTermLike,
    isBottom,
    isTop,
    patternSort,
    splitTerm,
    toTermLike,
    topOf,
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
import Kore.Internal.TermLike qualified as TermLike (
    hasFreeVariable,
    markSimplified,
 )
import Kore.Internal.TermLike qualified as TermLike.DoNotUse
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Prelude.Kore

-- TODO: Move Forall up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.

{- | 'simplify' simplifies an 'Forall' pattern with an 'OrPattern'
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
    | Pattern.isTop patt = Pattern.topOf sort
    | Pattern.isBottom patt = Pattern.bottomOf sort
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
    sort = Pattern.patternSort patt
    (term, predicate) = Pattern.splitTerm patt
    someVariable = mkSomeVariable variable
    someVariableName = variableName someVariable
    variableInTerm = TermLike.hasFreeVariable someVariableName term
    variableInCondition = Condition.hasFreeVariable someVariableName predicate
    termIsBoolean = isTop term || isBottom term
    predicateIsBoolean = isTop predicate || isBottom predicate
