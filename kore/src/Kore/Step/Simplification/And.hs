{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.And (
    makeEvaluate,
    simplify,
    And (..),
    termAnd,
) where

import Control.Error (
    runMaybeT,
 )
import Data.Bifunctor (
    bimap,
 )
import Data.List (
    foldl1',
 )
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike (
    And (..),
    TermLike,
    mkAnd,
    mkBottom_,
    mkNot,
    pattern And_,
    pattern Not_,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.AndTerms (
    maybeTermAnd,
 )
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Substitution as Substitution
import Kore.Unification.UnifierT (
    UnifierT (..),
    runUnifierT,
 )
import Logic
import Prelude.Kore

{- | Simplify a conjunction of 'OrPattern'.
To do that, it first distributes the terms, making it an Or of And patterns,
each And having 'Pattern's as children, then it simplifies each of
those.
Since an Pattern is of the form term /\ predicate /\ substitution,
making an and between two Patterns roughly means and-ing each of their
components separately.
This means that a bottom component anywhere makes the result bottom, while
top can always be ignored.
When we 'and' two terms:
by Proposition 5.24 from (1),
    x and functional-pattern = functional-pattern and [x=phi]
We can generalize that to:
    x and function-pattern
        = function-pattern and ceil(function-pattern) and [x=phi]
        but note that ceil(function-pattern) is not actually needed.
We can still generalize that to:
    function-like-pattern1 and function-like-pattern2
        = function-pattern1 and function-pattern1 == function-pattern2
Also, we have
    constructor1(s1, ..., sk) and constructor2(t1, ..., tk):
        if constructor1 != constructor2 then this is bottom
        else it is
            constructor1(s1 and t1, ..., sk and tk)
    * constructor - 'inj' (sort injection) pairs become bottom
    * injection-injection pairs with the same injection work the same as
      identical constructors
    domain-value1 and domain-value1, where both are string-based:
        domain-value1 if they are equal
        bottom otherwise
    the same for two string literals and two chars
-}
simplify ::
    MonadSimplify simplifier =>
    NotSimplifier (UnifierT simplifier) ->
    SideCondition RewritingVariableName ->
    MultiAnd (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify notSimplifier sideCondition orPatterns =
    OrPattern.observeAllT $ do
        patterns <- MultiAnd.traverse scatter orPatterns
        makeEvaluate notSimplifier sideCondition patterns

{- | 'makeEvaluate' simplifies a 'MultiAnd' of 'Pattern's.
See the comment for 'simplify' to find more details.
-}
makeEvaluate ::
    forall simplifier.
    HasCallStack =>
    MonadSimplify simplifier =>
    NotSimplifier (UnifierT simplifier) ->
    SideCondition RewritingVariableName ->
    MultiAnd (Pattern RewritingVariableName) ->
    LogicT simplifier (Pattern RewritingVariableName)
makeEvaluate notSimplifier sideCondition patterns
    | isBottom patterns = empty
    | Pattern.isTop patterns = return Pattern.top
    | otherwise = makeEvaluateNonBool notSimplifier sideCondition patterns

makeEvaluateNonBool ::
    forall simplifier.
    HasCallStack =>
    MonadSimplify simplifier =>
    NotSimplifier (UnifierT simplifier) ->
    SideCondition RewritingVariableName ->
    MultiAnd (Pattern RewritingVariableName) ->
    LogicT simplifier (Pattern RewritingVariableName)
makeEvaluateNonBool notSimplifier sideCondition patterns = do
    let unify pattern1 term2 = do
            let (term1, condition1) = Pattern.splitTerm pattern1
            unified <- termAnd notSimplifier term1 term2
            pure (Pattern.andCondition unified condition1)
    unified <-
        foldlM
            unify
            Pattern.top
            (term <$> toList patterns)
    let substitutions =
            Pattern.substitution unified
                <> foldMap Pattern.substitution patterns
    normalized <-
        from @_ @(Condition _) substitutions
            & Substitution.normalize sideCondition
    let substitution = Pattern.substitution normalized
        predicates :: MultiAnd (Predicate RewritingVariableName)
        predicates =
            mconcat
                [ Predicate.toMultiAnd (predicate unified)
                , Predicate.toMultiAnd (predicate normalized)
                , foldMap (from @(Predicate _) . predicate) patterns
                ]
        term =
            applyAndIdempotenceAndFindContradictions
                (Conditional.term unified)
    let predicate =
            Predicate.fromMultiAnd predicates
                & Predicate.setSimplified simplified
        simplified = foldMap Predicate.simplifiedAttribute predicates
     in Pattern.withCondition term (from substitution <> from predicate)
            & return

applyAndIdempotenceAndFindContradictions ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
applyAndIdempotenceAndFindContradictions patt =
    if noContradictions
        then foldl1' mkAndSimplified . Set.toList $ Set.union terms negatedTerms
        else mkBottom_
  where
    (terms, negatedTerms) = splitIntoTermsAndNegations patt
    noContradictions = Set.disjoint (Set.map mkNot terms) negatedTerms
    mkAndSimplified a b =
        TermLike.setSimplified
            (TermLike.simplifiedAttribute a <> TermLike.simplifiedAttribute b)
            (mkAnd a b)

splitIntoTermsAndNegations ::
    TermLike RewritingVariableName ->
    ( Set (TermLike RewritingVariableName)
    , Set (TermLike RewritingVariableName)
    )
splitIntoTermsAndNegations =
    bimap Set.fromList Set.fromList
        . partitionWith termOrNegation
        . children
  where
    children ::
        TermLike RewritingVariableName -> [TermLike RewritingVariableName]
    children (And_ _ p1 p2) = children p1 ++ children p2
    children p = [p]

    -- Left is for regular terms, Right is negated terms
    termOrNegation ::
        TermLike RewritingVariableName ->
        Either
            (TermLike RewritingVariableName)
            (TermLike RewritingVariableName)
    termOrNegation t@(Not_ _ _) = Right t
    termOrNegation t = Left t

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = partitionEithers . fmap f

{- | Simplify the conjunction (@\\and@) of two terms.
The comment for 'simplify' describes all the special cases handled by this.
-}
termAnd ::
    forall simplifier.
    MonadSimplify simplifier =>
    HasCallStack =>
    NotSimplifier (UnifierT simplifier) ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    LogicT simplifier (Pattern RewritingVariableName)
termAnd notSimplifier p1 p2 =
    Logic.scatter
        =<< (lift . runUnifierT notSimplifier) (termAndWorker p1 p2)
  where
    termAndWorker ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        UnifierT simplifier (Pattern RewritingVariableName)
    termAndWorker first second =
        maybeTermAnd notSimplifier termAndWorker first second
            & runMaybeT
            & fmap (fromMaybe andPattern)
      where
        andPattern = Pattern.fromTermLike (mkAnd first second)
