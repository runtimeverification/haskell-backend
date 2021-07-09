{- |
Module      : Kore.Step.Simplification.Iff
Description : Tools for Iff pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Iff (
    makeEvaluate,
    simplify,
    simplifyEvaluated,
) where

import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike (
    markSimplified,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.And as And (
    simplify,
 )
import qualified Kore.Step.Simplification.Implies as Implies (
    simplifyEvaluated,
 )
import qualified Kore.Step.Simplification.Not as Not (
    makeEvaluate,
    notSimplifier,
    simplifyEvaluated,
 )
import Kore.Step.Simplification.Simplify
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
simplify sideCondition Iff{iffFirst = first, iffSecond = second} =
    simplifyEvaluated sideCondition first second

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
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyEvaluated
    sideCondition
    first
    second
        | OrPattern.isTrue first = return second
        | OrPattern.isFalse first = Not.simplifyEvaluated sideCondition second
        | OrPattern.isTrue second = return first
        | OrPattern.isFalse second = Not.simplifyEvaluated sideCondition first
        | otherwise = case (firstPatterns, secondPatterns) of
            ([firstP], [secondP]) -> return $ makeEvaluate firstP secondP
            _ -> do
                fwd <- Implies.simplifyEvaluated sideCondition first second
                bwd <- Implies.simplifyEvaluated sideCondition second first
                And.simplify
                    Not.notSimplifier
                    sideCondition
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
