{- |
Module      : Kore.Simplify.Iff
Description : Tools for Iff pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Iff (
    makeEvaluate,
    simplify,
    simplifyEvaluated,
) where

import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike
import Kore.Internal.TermLike qualified as TermLike (
    markSimplified,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.And qualified as And (
    simplify,
 )
import Kore.Simplify.Implies qualified as Implies (
    simplifyEvaluated,
 )
import Kore.Simplify.Not qualified as Not (
    makeEvaluate,
    notSimplifier,
    simplify,
 )
import Kore.Simplify.Simplify
import Prelude.Kore

{- |'simplify' simplifies an 'Iff' pattern with 'OrPattern'
children.

Right now this has special cases only for top and bottom children
and for children with top terms.
-}
simplify ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Iff Sort (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify sideCondition Iff{iffFirst = first, iffSecond = second, iffSort = sort} =
    simplifyEvaluated sort sideCondition first second

{- | evaluates an 'Iff' given its two 'OrPattern' children.

See 'simplify' for detailed documentation.
-}

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Iff Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated ::
    MonadSimplify simplifier =>
    Sort ->
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyEvaluated sort sideCondition first second
    | OrPattern.isTrue first = return second
    | OrPattern.isFalse first =
        Not.simplify sideCondition Not{notSort = sort, notChild = second}
    | OrPattern.isTrue second = return first
    | OrPattern.isFalse second =
        Not.simplify sideCondition Not{notSort = sort, notChild = first}
    | otherwise = case (firstPatterns, secondPatterns) of
        ([firstP], [secondP]) -> return $ makeEvaluate firstP secondP
        _ -> do
            fwd <- Implies.simplifyEvaluated sort sideCondition first second
            bwd <- Implies.simplifyEvaluated sort sideCondition second first
            (And.simplify sort Not.notSimplifier sideCondition)
                (MultiAnd.make [fwd, bwd])
  where
    firstPatterns = toList first
    secondPatterns = toList second

{- | evaluates an 'Iff' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluate first second
    | Pattern.isTop first = OrPattern.fromPatterns [second]
    | Pattern.isBottom first = Not.makeEvaluate second
    | Pattern.isTop second = OrPattern.fromPatterns [first]
    | Pattern.isBottom second = Not.makeEvaluate first
    | otherwise = makeEvaluateNonBoolIff first second

makeEvaluateNonBoolIff ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateNonBoolIff
    patt1@Conditional
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    patt2@Conditional
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
        | isTop firstTerm
          , isTop secondTerm =
            OrPattern.fromPatterns
                [ Conditional
                    { term = firstTerm
                    , predicate =
                        Predicate.markSimplified $
                            Predicate.makeIffPredicate
                                ( Predicate.makeAndPredicate
                                    firstPredicate
                                    (Substitution.toPredicate firstSubstitution)
                                )
                                ( Predicate.makeAndPredicate
                                    secondPredicate
                                    (Substitution.toPredicate secondSubstitution)
                                )
                    , substitution = mempty
                    }
                ]
        | otherwise =
            OrPattern.fromTermLike $
                TermLike.markSimplified $
                    mkIff
                        (Pattern.toTermLike patt1)
                        (Pattern.toTermLike patt2)
