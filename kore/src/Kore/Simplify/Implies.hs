{- |
Module      : Kore.Simplify.Implies
Description : Tools for Implies pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Implies (
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
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.And qualified as And
import Kore.Simplify.Not qualified as Not (
    makeEvaluate,
    notSimplifier,
    simplify,
 )
import Kore.Simplify.Simplify
import Logic (
    LogicT,
 )
import Logic qualified
import Prelude.Kore

{- |'simplify' simplifies an 'Implies' pattern with 'OrPattern'
children.

Right now this uses the following simplifications:

* a -> (b or c) = (a -> b) or (a -> c)
* bottom -> b = top
* top -> b = b
* a -> top = top
* a -> bottom = not a

and it has a special case for children with top terms.
-}
simplify ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Implies Sort (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify
    sideCondition
    Implies{impliesFirst = first, impliesSecond = second, impliesSort = sort} =
        simplifyEvaluated sort sideCondition first second

{- | simplifies an Implies given its two 'OrPattern' children.

See 'simplify' for details.
-}

-- TODO: Maybe transform this to (not a) \/ b
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Implies Sort) (Attribute.Pattern variable) (OrPattern variable)

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
    | OrPattern.isFalse first = return (OrPattern.topOf sort)
    | OrPattern.isTrue second = return (OrPattern.topOf sort)
    | OrPattern.isFalse second =
        Not.simplify sideCondition Not{notSort = sort, notChild = first}
    | otherwise =
        OrPattern.observeAllT $
            Logic.scatter second
                >>= simplifyEvaluateHalfImplies sort sideCondition first

simplifyEvaluateHalfImplies ::
    MonadSimplify simplifier =>
    Sort ->
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    LogicT simplifier (Pattern RewritingVariableName)
simplifyEvaluateHalfImplies sort sideCondition first second
    | OrPattern.isTrue first = return second
    | OrPattern.isFalse first = return (Pattern.topOf sort)
    | Pattern.isTop second = return (Pattern.topOf sort)
    | Pattern.isBottom second =
        Not.simplify sideCondition Not{notSort = sort, notChild = first}
            >>= Logic.scatter
    | otherwise =
        case toList first of
            [firstP] -> Logic.scatter $ makeEvaluateImplies firstP second
            firstPatterns ->
                distributeEvaluateImplies sideCondition firstPatterns second
                    >>= Logic.scatter

distributeEvaluateImplies ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
distributeEvaluateImplies sideCondition firsts second =
    (And.simplify sort Not.notSimplifier sideCondition)
        (MultiAnd.make implications)
  where
    sort = Pattern.patternSort second
    implications = map (\first -> makeEvaluateImplies first second) firsts

makeEvaluateImplies ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateImplies
    first
    second
        | Pattern.isTop first =
            OrPattern.fromPatterns [second]
        | Pattern.isBottom first =
            OrPattern.fromPatterns [Pattern.topOf sort]
        | Pattern.isTop second =
            OrPattern.fromPatterns [Pattern.topOf sort]
        | Pattern.isBottom second =
            Not.makeEvaluate first
        | otherwise =
            makeEvaluateImpliesNonBool first second
      where
        sort = Pattern.patternSort first

makeEvaluateImpliesNonBool ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateImpliesNonBool
    pattern1@Conditional
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    pattern2@Conditional
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
                            Predicate.makeImpliesPredicate
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
            -- TODO (thomas.tuegel): Maybe this should be an error?
            OrPattern.fromPatterns
                [ Conditional
                    { term =
                        TermLike.markSimplified $
                            mkImplies
                                (Pattern.toTermLike pattern1)
                                (Pattern.toTermLike pattern2)
                    , predicate = Predicate.makeTruePredicate
                    , substitution = mempty
                    }
                ]
