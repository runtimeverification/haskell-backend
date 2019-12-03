{-|
Module      : Kore.Step.Simplification.Equals
Description : Tools for Equals pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Equals
    ( makeEvaluate
    , makeEvaluateTermsToPredicate
    , simplify
    , termEquals
    ) where

import Control.Error
    ( MaybeT (..)
    )
import Control.Monad
    ( foldM
    )
import Data.List
    ( foldl'
    )
import Data.Maybe
    ( fromMaybe
    )
import qualified GHC.Stack as GHC

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( pattern PredicateTrue
    , makeEqualsPredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.And as And
    ( simplifyEvaluated
    )
import qualified Kore.Step.Simplification.AndPredicates as And
    ( simplifyEvaluatedMultiPredicate
    )
import Kore.Step.Simplification.AndTerms
    ( maybeTermEquals
    )
import {-# SOURCE #-} qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluate
    , makeEvaluateTerm
    )
import qualified Kore.Step.Simplification.Iff as Iff
    ( makeEvaluate
    , simplifyEvaluated
    )
import qualified Kore.Step.Simplification.Implies as Implies
    ( simplifyEvaluated
    )
import qualified Kore.Step.Simplification.Not as Not
    ( simplifyEvaluated
    , simplifyEvaluatedPredicate
    )
import qualified Kore.Step.Simplification.Or as Or
    ( simplifyEvaluated
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.UnifierT
    ( runUnifierT
    )
import Kore.Unification.Unify
    ( MonadUnify
    )

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
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> Equals Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify predicate Equals { equalsFirst = first, equalsSecond = second } =
    simplifyEvaluated predicate first second

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Equals Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> OrPattern variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated predicate first second
  | first == second = return OrPattern.top
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise = do
    let isFunctionConditional Conditional {term} = isFunctionPattern term
    case (firstPatterns, secondPatterns) of
        ([firstP], [secondP]) ->
            makeEvaluate firstP secondP predicate
        ([firstP], _)
            | isFunctionConditional firstP ->
                makeEvaluateFunctionalOr predicate firstP secondPatterns
        (_, [secondP])
            | isFunctionConditional secondP ->
                makeEvaluateFunctionalOr predicate secondP firstPatterns
        _
            | OrPattern.isPredicate first && OrPattern.isPredicate second ->
                Iff.simplifyEvaluated first second
            | otherwise ->
                makeEvaluate
                    (OrPattern.toPattern first)
                    (OrPattern.toPattern second)
                    predicate
  where
    firstPatterns = MultiOr.extractPatterns first
    secondPatterns = MultiOr.extractPatterns second

makeEvaluateFunctionalOr
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> Pattern variable
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeEvaluateFunctionalOr predicate first seconds = do
    firstCeil <- Ceil.makeEvaluate predicate first
    secondCeilsWithProofs <- mapM (Ceil.makeEvaluate predicate) seconds
    firstNotCeil <- Not.simplifyEvaluated firstCeil
    let secondCeils = secondCeilsWithProofs
    secondNotCeils <- traverse Not.simplifyEvaluated secondCeils
    let oneNotBottom = foldl' Or.simplifyEvaluated OrPattern.bottom secondCeils
    allAreBottom <-
        foldM
            And.simplifyEvaluated
            (OrPattern.fromPatterns [Pattern.top])
            (firstNotCeil : secondNotCeils)
    firstEqualsSeconds <-
        mapM
            (makeEvaluateEqualsIfSecondNotBottom first)
            (zip seconds secondCeils)
    oneIsNotBottomEquals <-
        foldM
            And.simplifyEvaluated
            firstCeil
            (oneNotBottom : firstEqualsSeconds)
    return (MultiOr.merge allAreBottom oneIsNotBottomEquals)
  where
    makeEvaluateEqualsIfSecondNotBottom
        Conditional {term = firstTerm}
        (Conditional {term = secondTerm}, secondCeil)
      = do
        equality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
        Implies.simplifyEvaluated secondCeil equality

{-| evaluates an 'Equals' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Pattern variable
    -> Pattern variable
    -> Condition variable
    -> simplifier (OrPattern variable)
makeEvaluate
    first@Conditional { term = Top_ _ }
    second@Conditional { term = Top_ _ }
    _
  =
    return
        (Iff.makeEvaluate
            first {term = mkTop_}   -- remove the term's sort
            second {term = mkTop_}  -- remove the term's sort
        )
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
    predicate
  = do
    result <- makeEvaluateTermsToPredicate firstTerm secondTerm predicate
    return (Pattern.fromCondition <$> result)

makeEvaluate
    first@Conditional { term = firstTerm }
    second@Conditional { term = secondTerm }
    predicate
  = do
    let first' = first { term = if termsAreEqual then mkTop_ else firstTerm }
    firstCeil <- Ceil.makeEvaluate predicate first'
    let second' = second { term = if termsAreEqual then mkTop_ else secondTerm }
    secondCeil <- Ceil.makeEvaluate predicate second'
    firstCeilNegation <- Not.simplifyEvaluated firstCeil
    secondCeilNegation <- Not.simplifyEvaluated secondCeil
    termEquality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
    negationAnd <- And.simplifyEvaluated firstCeilNegation secondCeilNegation
    ceilAnd <- And.simplifyEvaluated firstCeil secondCeil
    equalityAnd <- And.simplifyEvaluated termEquality ceilAnd
    return $ Or.simplifyEvaluated equalityAnd negationAnd
  where
    termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> TermLike variable
    -> simplifier (OrPattern variable)
makeEvaluateTermsAssumesNoBottom firstTerm secondTerm = do
    result <-
        runMaybeT
        $ makeEvaluateTermsAssumesNoBottomMaybe firstTerm secondTerm
    (return . fromMaybe def) result
  where
    def =
        OrPattern.fromPattern
            Conditional
                { term = mkTop_
                , predicate =
                    Predicate.markSimplified
                    $ makeEqualsPredicate_ firstTerm secondTerm
                , substitution = mempty
                }

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottomMaybe
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> TermLike variable
    -> MaybeT simplifier (OrPattern variable)
makeEvaluateTermsAssumesNoBottomMaybe first second = do
    result <- termEquals first second
    return (Pattern.fromCondition <$> result)

{-| Combines two terms with 'Equals' into a predicate-substitution.

It does not attempt to fully simplify the terms (the not-ceil parts used to
catch the bottom=bottom case and everything above it), but, if the patterns are
total, this should not be needed anyway.
TODO(virgil): Fully simplify the terms (right now we're not simplifying not
because it returns an 'or').

See 'simplify' for detailed documentation.
-}
makeEvaluateTermsToPredicate
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> TermLike variable
    -> Condition variable
    -> simplifier (OrCondition variable)
makeEvaluateTermsToPredicate first second configurationCondition
  | first == second = return OrCondition.top
  | otherwise = do
    result <- runMaybeT $ termEquals first second
    case result of
        Nothing ->
            return
                $ OrCondition.fromCondition . Condition.fromPredicate
                $ Predicate.markSimplified
                $ makeEqualsPredicate_ first second
        Just predicatedOr -> do
            firstCeilOr <- Ceil.makeEvaluateTerm configurationCondition first
            secondCeilOr <- Ceil.makeEvaluateTerm configurationCondition second
            firstCeilNegation <- Not.simplifyEvaluatedPredicate firstCeilOr
            secondCeilNegation <- Not.simplifyEvaluatedPredicate secondCeilOr
            ceilNegationAnd <- And.simplifyEvaluatedMultiPredicate
                (MultiAnd.make [firstCeilNegation, secondCeilNegation])

            return $ MultiOr.merge predicatedOr ceilNegationAnd

{- | Simplify an equality relation of two patterns.

@termEquals@ assumes the result will be part of a predicate with a special
condition for testing @⊥ = ⊥@ equality.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

 -}
termEquals
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT simplifier (OrCondition variable)
termEquals first second = MaybeT $ do
    maybeResults <- BranchT.gather $ runMaybeT $ termEqualsAnd first second
    case sequence maybeResults of
        Nothing -> return Nothing
        Just results -> return $ Just $
            MultiOr.make (map Condition.eraseConditionalTerm results)

termEqualsAnd
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT (BranchT simplifier) (Pattern variable)
termEqualsAnd p1 p2 =
    MaybeT $ run $ maybeTermEqualsWorker p1 p2
  where
    run it = (runUnifierT . runMaybeT) it >>= either missingCase BranchT.scatter
    missingCase = const (return Nothing)

    maybeTermEqualsWorker
        :: forall unifier
        .  MonadUnify unifier
        => TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)
    maybeTermEqualsWorker = maybeTermEquals termEqualsAndWorker

    termEqualsAndWorker
        :: forall unifier
        .  MonadUnify unifier
        => TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termEqualsAndWorker first second =
        either ignoreErrors scatterResults
        =<< (runUnifierT . runMaybeT) (maybeTermEqualsWorker first second)
      where
        ignoreErrors _ = return equalsPredicate
        scatterResults =
            maybe
                (return equalsPredicate) -- default if no results
                (BranchT.alternate . BranchT.scatter)
            . sequence
        equalsPredicate =
            Conditional
                { term = mkTop_
                , predicate =
                    Predicate.markSimplified
                    $ makeEqualsPredicate_ first second
                , substitution = mempty
                }
