{- |
Module      : Kore.Simplify.Equals
Description : Tools for Equals pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Equals (
    makeEvaluate,
    makeEvaluateTermsToPredicate,
    simplify,
    termEquals,
) where

import Control.Error (
    MaybeT (..),
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrCondition qualified as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeEqualsPredicate,
    pattern PredicateTrue,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.And qualified as And (
    simplify,
 )
import Kore.Simplify.AndPredicates qualified as And (
    simplifyEvaluatedMultiPredicate,
 )
import Kore.Simplify.AndTerms (
    compareForEquals,
    maybeTermEquals,
 )
import Kore.Simplify.Iff qualified as Iff (
    makeEvaluate,
    simplifyEvaluated,
 )
import Kore.Simplify.Implies qualified as Implies (
    simplifyEvaluated,
 )
import Kore.Simplify.Not qualified as Not (
    notSimplifier,
    simplify,
    simplifyEvaluatedPredicate,
 )
import Kore.Simplify.Or qualified as Or (
    simplifyEvaluated,
 )
import Kore.Simplify.Simplify
import Kore.Sort (sameSort)
import Kore.Unification.UnifierT (
    runUnifierT,
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import Logic (
    LogicT,
 )
import Logic qualified
import Prelude.Kore

{- ORMOLU_DISABLE -}
{-|'simplify' simplifies an 'Equals' pattern made of 'OrPattern's.

This uses the following simplifications
(t = term, s = substitution, p = predicate):

* Equals(a, a) = true
* Equals(phi, psi1 or psi2 or ... or psin), when phi is functional
    = or
        ( not ceil (phi) and not ceil(psi1) and ... and not ceil (psin)
        , and
            ( ceil(phi)
            , ceil(psi1) or ceil(psi2) or  ... or ceil(psin)
            , ceil(psi1) implies phi == psi1)
            , ceil(psi2) implies phi == psi2)
            ...
            , ceil(psin) implies phi == psin)
            )
        )
* Equals(t1 and t2) = ceil(t1 and t2) or (not ceil(t1) and not ceil(t2))
    if t1 and t2 are functions.
* Equals(t1 and p1 and s1, t2 and p2 and s2) =
    Or(
        And(
            Equals(t1, t2)
            And(ceil(t1) and p1 and s1, ceil(t2) and p2 and s2))
        And(not(ceil(t1) and p1 and s1), not(ceil(t2) and p2 and s2))
    )
    + If t1 and t2 can't be bottom, then this becomes
      Equals(t1 and p1 and s1, t2 and p2 and s2) =
        Or(
            And(
                Equals(t1, t2)
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the two terms are constructors, then this becomes
      Equals(
        constr1(t1, t2, ...) and p1 and s1,
        constr2(t1', t2', ...) and p2 and s2)
        = Or(
            and(
                (p1 and s2) iff (p2 and s2),
                constr1 == constr2,
                ceil(constr1(t1, t2, ...), constr2(t1', t2', ...))
                Equals(t1, t1'), Equals(t2, t2'), ...
                )
            and(
                not(ceil(constr1(t1, t2, ...)) and p1 and s1),
                not(ceil(constr2(t1', t2', ...)), p2 and s2)
                )
        )
      Note that when expanding Equals(t1, t1') recursively we don't need to
      put the ceil conditions again, since we already asserted that.
      Also note that ceil(constr(...)) is simplifiable.
    + If the first term is a variable and the second is functional,
      then we get a substitution:
        Or(
            And(
                [t1 = t2]
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the terms are Top, this becomes
      Equals(p1 and s1, p2 and s2) = Iff(p1 and s1, p2 and s2)
    + If the predicate and substitution are Top, then the result is any of
      Equals(t1, t2)
      Or(
          Equals(t1, t2)
          And(not(ceil(t1) and p1 and s1), not(ceil(t2) and p2 and s2))
      )

Normalization of the compared terms is not implemented yet, so
Equals(a and b, b and a) will not be evaluated to Top.
-}
{- ORMOLU_ENABLE -}
simplify ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Equals Sort (OrPattern RewritingVariableName) ->
    simplifier (OrCondition RewritingVariableName)
simplify
    sideCondition
    Equals
        { equalsFirst = first
        , equalsSecond = second
        , equalsOperandSort = sort
        } = simplifyEvaluated sort sideCondition first' second'
      where
        (first', second') =
            minMaxBy (on compareForEquals (OrPattern.toTermLike sort)) first second

{-

Another way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Equals Sort) (Attribute.Pattern variable) (OrPattern variable)

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
    simplifier (OrCondition RewritingVariableName)
simplifyEvaluated sort sideCondition first second
    | first == second = return OrCondition.top
    -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
    | otherwise = do
        let isFunctionConditional Conditional{term} = isFunctionPattern term
        case (firstPatterns, secondPatterns) of
            ([firstP], [secondP]) ->
                makeEvaluate firstP secondP sideCondition
            ([firstP], _)
                | isFunctionConditional firstP ->
                    makeEvaluateFunctionalOr sideCondition firstP secondPatterns
            (_, [secondP])
                | isFunctionConditional secondP ->
                    makeEvaluateFunctionalOr sideCondition secondP firstPatterns
            _
                | OrPattern.isPredicate first && OrPattern.isPredicate second ->
                    Iff.simplifyEvaluated sort sideCondition first second
                        & fmap (MultiOr.map Pattern.withoutTerm)
                | otherwise ->
                    makeEvaluate
                        (OrPattern.toPattern sort first)
                        (OrPattern.toPattern sort second)
                        sideCondition
  where
    firstPatterns = toList first
    secondPatterns = toList second

makeEvaluateFunctionalOr ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluateFunctionalOr sideCondition first seconds = do
    let sort = Pattern.patternSort first
    firstCeil <- makeEvaluateCeil sort sideCondition first
    secondCeilsWithProofs <- mapM (makeEvaluateCeil sort sideCondition) seconds
    let mkNotSimplified notChild =
            Not.simplify sideCondition Not{notSort = sort, notChild}
    firstNotCeil <- mkNotSimplified firstCeil
    let secondCeils = secondCeilsWithProofs
    secondNotCeils <- traverse mkNotSimplified secondCeils
    let oneNotBottom = foldl' Or.simplifyEvaluated OrPattern.bottom secondCeils
    allAreBottom <-
        (And.simplify sort Not.notSimplifier sideCondition)
            (MultiAnd.make (firstNotCeil : secondNotCeils))
    firstEqualsSeconds <-
        mapM
            (makeEvaluateEqualsIfSecondNotBottom sort first)
            (zip seconds secondCeils)
    oneIsNotBottomEquals <-
        (And.simplify sort Not.notSimplifier sideCondition)
            (MultiAnd.make (firstCeil : oneNotBottom : firstEqualsSeconds))
    MultiOr.merge allAreBottom oneIsNotBottomEquals
        & MultiOr.map Pattern.withoutTerm
        & return
  where
    makeEvaluateEqualsIfSecondNotBottom
        sort
        Conditional{term = firstTerm}
        (Conditional{term = secondTerm}, secondCeil) =
            do
                equality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
                Implies.simplifyEvaluated sort sideCondition secondCeil equality

{- | evaluates an 'Equals' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate ::
    MonadSimplify simplifier =>
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluate
    first@Conditional{term = Top_ _}
    second@Conditional{term = Top_ _}
    _ =
        Iff.makeEvaluate
            first
            second
            & MultiOr.map Pattern.withoutTerm
            & return
makeEvaluate
    Conditional
        { term = firstTerm
        , predicate = PredicateTrue
        , substitution = (Substitution.unwrap -> [])
        }
    Conditional
        { term = secondTerm
        , predicate = PredicateTrue
        , substitution = (Substitution.unwrap -> [])
        }
    sideCondition =
        makeEvaluateTermsToPredicate firstTerm secondTerm sideCondition
makeEvaluate
    first@Conditional{term = firstTerm}
    second@Conditional{term = secondTerm}
    sideCondition =
        do
            let first' = first{term = if termsAreEqual then mkTop sort else firstTerm}
            firstCeil <- makeEvaluateCeil sort sideCondition first'
            let second' = second{term = if termsAreEqual then mkTop sort else secondTerm}
            secondCeil <- makeEvaluateCeil sort sideCondition second'
            let mkNotSimplified notChild =
                    Not.simplify sideCondition Not{notSort = sort, notChild}
            firstCeilNegation <- mkNotSimplified firstCeil
            secondCeilNegation <- mkNotSimplified secondCeil
            termEquality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
            negationAnd <-
                (And.simplify sort Not.notSimplifier sideCondition)
                    (MultiAnd.make [firstCeilNegation, secondCeilNegation])
            equalityAnd <-
                (And.simplify sort Not.notSimplifier sideCondition)
                    (MultiAnd.make [termEquality, firstCeil, secondCeil])
            Or.simplifyEvaluated equalityAnd negationAnd
                & MultiOr.map Pattern.withoutTerm
                & return
      where
        sort = sameSort (termLikeSort firstTerm) (termLikeSort secondTerm)
        termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom ::
    MonadSimplify simplifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
makeEvaluateTermsAssumesNoBottom firstTerm secondTerm = do
    result <-
        runMaybeT $
            makeEvaluateTermsAssumesNoBottomMaybe firstTerm secondTerm
    (return . fromMaybe def) result
  where
    sort = termLikeSort firstTerm
    def =
        OrPattern.fromPattern
            Conditional
                { term = mkTop sort
                , predicate =
                    Predicate.markSimplified $
                        makeEqualsPredicate firstTerm secondTerm
                , substitution = mempty
                }

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottomMaybe ::
    forall simplifier.
    MonadSimplify simplifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT simplifier (OrPattern RewritingVariableName)
makeEvaluateTermsAssumesNoBottomMaybe first second = do
    result <- termEquals first second
    let sort = termLikeSort first
    return (MultiOr.map (Pattern.fromCondition sort) result)

{- | Combines two terms with 'Equals' into a predicate-substitution.

It does not attempt to fully simplify the terms (the not-ceil parts used to
catch the bottom=bottom case and everything above it), but, if the patterns are
total, this should not be needed anyway.
TODO(virgil): Fully simplify the terms (right now we're not simplifying not
because it returns an 'or').

See 'simplify' for detailed documentation.
-}
makeEvaluateTermsToPredicate ::
    MonadSimplify simplifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluateTermsToPredicate first second sideCondition
    | first == second = return OrCondition.top
    | otherwise = do
        result <- runMaybeT $ termEquals first second
        case result of
            Nothing ->
                return $
                    OrCondition.fromCondition . Condition.fromPredicate $
                        Predicate.markSimplified $
                            makeEqualsPredicate first second
            Just predicatedOr -> do
                firstCeilOr <- makeEvaluateTermCeil sideCondition first
                secondCeilOr <- makeEvaluateTermCeil sideCondition second
                firstCeilNegation <- Not.simplifyEvaluatedPredicate firstCeilOr
                secondCeilNegation <- Not.simplifyEvaluatedPredicate secondCeilOr
                ceilNegationAnd <-
                    And.simplifyEvaluatedMultiPredicate
                        sideCondition
                        (MultiAnd.make [firstCeilNegation, secondCeilNegation])

                return $ MultiOr.merge predicatedOr ceilNegationAnd

{- | Simplify an equality relation of two patterns.

@termEquals@ assumes the result will be part of a predicate with a special
condition for testing @⊥ = ⊥@ equality.

The comment for 'Kore.Simplify.And.simplify' describes all
the special cases handled by this.
-}
termEquals ::
    MonadSimplify simplifier =>
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT simplifier (OrCondition RewritingVariableName)
termEquals first second = MaybeT $ do
    maybeResults <- Logic.observeAllT $ runMaybeT $ termEqualsAnd first second
    case sequence maybeResults of
        Nothing -> return Nothing
        Just results ->
            return $
                Just $
                    MultiOr.make (map Condition.eraseConditionalTerm results)

termEqualsAnd ::
    forall simplifier.
    MonadSimplify simplifier =>
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT (LogicT simplifier) (Pattern RewritingVariableName)
termEqualsAnd p1 p2 =
    MaybeT $ run $ maybeTermEqualsWorker p1 p2
  where
    run it =
        (runUnifierT Not.notSimplifier . runMaybeT) it
            >>= Logic.scatter

    maybeTermEqualsWorker ::
        forall unifier.
        MonadUnify unifier =>
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        MaybeT unifier (Pattern RewritingVariableName)
    maybeTermEqualsWorker =
        maybeTermEquals Not.notSimplifier termEqualsAndWorker

    termEqualsAndWorker ::
        forall unifier.
        MonadUnify unifier =>
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (Pattern RewritingVariableName)
    termEqualsAndWorker first second =
        scatterResults
            =<< runUnification (maybeTermEqualsWorker first second)
      where
        runUnification = runUnifierT Not.notSimplifier . runMaybeT
        scatterResults =
            maybe
                (return equalsPattern) -- default if no results
                Logic.scatter
                . sequence
        equalsPattern =
            makeEqualsPredicate first second
                & Predicate.markSimplified
                & Condition.fromPredicate
                -- Although the term will eventually be discarded, the sub-term
                -- unifier should return it in case the caller needs to
                -- reconstruct the unified term. If we returned \top here, then
                -- the unified pattern wouldn't be a function-like term. Because the
                -- terms are equal, it does not matter which one is returned; we
                -- prefer the first term because this is the "configuration" side
                -- during rule unification.
                & Pattern.withCondition first
