{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Step.Simplification.And
    ( makeEvaluate
    , simplify
    , And (..)
    , termAnd
    ) where

import Prelude.Kore

import Control.Error
    ( runMaybeT
    )
import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.State.Strict as State
import Data.Bifunctor
    ( bimap
    )
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.List
    ( foldl1'
    , sortOn
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Traversable
    ( for
    )
import Data.Tuple.Extra
    ( (***)
    )
import qualified Data.Tuple.Extra as Tuple
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd

import Changed
import Kore.Attribute.Synthetic
    ( synthesize
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeFalsePredicate
    , makeTruePredicate
    , pattern PredicateNot
    , pattern PredicateExists
    , pattern PredicateForall
    , pattern PredicateEquals
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.Symbol
    ( isConstructor
    , isFunction
    )
import Kore.Internal.TermLike
    ( And (..)
    , pattern And_
    , pattern App_
    , pattern Builtin_
    , pattern Equals_
    , pattern Exists_
    , pattern Forall_
    , pattern Inj_
    , pattern Mu_
    , pattern Not_
    , pattern Nu_
    , TermLike
    , Variable (..)
    , mkAnd
    , mkBottom_
    , mkNot
    , mkEquals_
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.AndTerms
    ( maybeTermAnd
    )
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Substitution as Substitution
import Kore.Unification.UnifierT
    ( UnifierT (..)
    , runUnifierT
    )
import Logic
import Pair

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
simplify
    :: InternalVariable variable
    => MonadSimplify simplifier
    => NotSimplifier (UnifierT simplifier)
    -> SideCondition variable
    -> MultiAnd (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify notSimplifier sideCondition orPatterns =
    OrPattern.observeAllT $ do
        patterns <- MultiAnd.traverse scatter orPatterns
        makeEvaluate notSimplifier sideCondition patterns

{- | 'makeEvaluate' simplifies a 'MultiAnd' of 'Pattern's.

See the comment for 'simplify' to find more details.

-}
makeEvaluate
    :: forall variable simplifier
    .  HasCallStack
    => InternalVariable variable
    => MonadSimplify simplifier
    => NotSimplifier (UnifierT simplifier)
    -> SideCondition variable
    -> MultiAnd (Pattern variable)
    -> LogicT simplifier (Pattern variable)
makeEvaluate notSimplifier sideCondition patterns
  | isBottom patterns = empty
  | Pattern.isTop patterns = return Pattern.top
  | otherwise = makeEvaluateNonBool notSimplifier sideCondition patterns

makeEvaluateNonBool
    :: forall variable simplifier
    .  HasCallStack
    => InternalVariable variable
    => MonadSimplify simplifier
    => NotSimplifier (UnifierT simplifier)
    -> SideCondition variable
    -> MultiAnd (Pattern variable)
    -> LogicT simplifier (Pattern variable)
makeEvaluateNonBool notSimplifier sideCondition patterns = do
    let unify pattern1 term2 = do
            let (term1, condition1) = Pattern.splitTerm pattern1
            unified <- termAnd notSimplifier term1 term2
            pure (Pattern.andCondition unified condition1)
    unified <-
        Foldable.foldlM
            unify
            Pattern.top
            (term <$> Foldable.toList patterns)
    let substitutions =
            Pattern.substitution unified
            <> foldMap Pattern.substitution patterns
    normalized <-
        from @_ @(Condition _) substitutions
        & Substitution.normalize sideCondition
    let substitution = Pattern.substitution normalized
        predicates :: Changed (MultiAnd (Predicate variable))
        predicates =
            mconcat
                [ MultiAnd.fromPredicate (predicate unified)
                , MultiAnd.fromPredicate (predicate normalized)
                , foldMap (from @(Predicate _) . predicate) patterns
                ]
            & simplifyConjunctionByAssumption
        term =
            applyAndIdempotenceAndFindContradictions
                (Conditional.term unified)
    case predicates of
        Unchanged unchanged ->
            Pattern.withCondition term (from substitution <> from predicate)
            & return
          where
            predicate =
                MultiAnd.toPredicate unchanged
                & Predicate.setSimplified simplified
            simplified = foldMap Predicate.simplifiedAttribute unchanged
        Changed changed ->
            Pattern.withCondition term (from substitution <> from predicate)
            & simplifyCondition sideCondition
          where
            predicate = MultiAnd.toPredicate changed

{- | Simplify the conjunction of 'Predicate' clauses by assuming each is true.

The conjunction is simplified by the identity:

@
A ∧ P(A) = A ∧ P(⊤)
@

 -}
simplifyConjunctionByAssumption
    :: forall variable
    .  InternalVariable variable
    => MultiAnd (Predicate variable)
    -> Changed (MultiAnd (Predicate variable))
simplifyConjunctionByAssumption (Foldable.toList -> andPredicates) =
    fmap MultiAnd.make
    $ flip evalStateT (HashMap.empty, HashMap.empty)
    $ for (sortBySize andPredicates)
    $ \original -> do
        result <- applyAssumptions original
        assume result
        return result
  where
    -- Sorting by size ensures that every clause is considered before any clause
    -- which could contain it, because the containing clause is necessarily
    -- larger.
    sortBySize :: [Predicate variable] -> [Predicate variable]
    sortBySize = sortOn predSize

    size :: TermLike variable -> Int
    size =
        Recursive.fold $ \(_ :< termLikeF) ->
            case termLikeF of
                TermLike.EvaluatedF evaluated -> TermLike.getEvaluated evaluated
                TermLike.DefinedF defined -> TermLike.getDefined defined
                _ -> 1 + Foldable.sum termLikeF

    predSize :: Predicate variable -> Int
    predSize =
        Recursive.fold $ \(_ :< predF) ->
            case predF of
                Predicate.CeilF ceil_ -> 1 + Foldable.sum (size <$> ceil_)
                Predicate.EqualsF equals_ -> 1 + Foldable.sum (size <$> equals_)
                Predicate.FloorF floor_ -> 1 + Foldable.sum (size <$> floor_)
                Predicate.InF in_ -> 1 + Foldable.sum (size <$> in_)
                _ -> 1 + Foldable.sum predF

    assume
        :: Predicate variable ->
        StateT 
            ( HashMap (TermLike variable) (TermLike variable)
            , HashMap (Predicate variable) (Predicate variable))
            Changed ()
    assume predicate =
        State.modify' (assumeEqualTerms . assumePredicate)
      where
        assumePredicate =
            case predicate of
                PredicateNot notChild ->
                    -- Infer that the predicate is \bottom.
                    Tuple.second $ HashMap.insert notChild makeFalsePredicate
                _ ->
                    -- Infer that the predicate is \top.
                    Tuple.second $ HashMap.insert predicate makeTruePredicate
        assumeEqualTerms =
            case predicate of
                PredicateEquals t1 t2 ->
                    case retractLocalFunction (mkEquals_ t1 t2) of
                        Just (Pair t1' t2') -> Tuple.first $ HashMap.insert t1' t2'
                        _ -> id
                _ -> id

    applyAssumptions
        ::  Predicate variable
        ->  StateT
            ( HashMap (TermLike variable) (TermLike variable)
            , HashMap (Predicate variable) (Predicate variable))
            Changed (Predicate variable)
    applyAssumptions replaceIn = do
        assumptions <- State.get
        lift (applyAssumptionsWorker assumptions replaceIn)

    applyAssumptionsWorker
        :: ( HashMap (TermLike variable) (TermLike variable)
           , HashMap (Predicate variable) (Predicate variable))
        -> Predicate variable
        -> Changed (Predicate variable)
    applyAssumptionsWorker assumptions original
      | Just result <- HashMap.lookup original (snd assumptions) = Changed result

      | HashMap.null (fst assumptions') &&
        HashMap.null (snd assumptions') = Unchanged original

      | otherwise = (case replaceIn of
          Predicate.CeilF ceil_ -> Predicate.CeilF <$> traverse
                             (applyAssumptionsWorkerTerm (fst assumptions')) ceil_
          Predicate.FloorF floor_ -> Predicate.FloorF <$> traverse
                             (applyAssumptionsWorkerTerm (fst assumptions')) floor_
          Predicate.EqualsF equals_ -> Predicate.EqualsF <$> traverse
                             (applyAssumptionsWorkerTerm (fst assumptions')) equals_
          Predicate.InF in_ -> Predicate.InF <$> traverse
                             (applyAssumptionsWorkerTerm (fst assumptions')) in_
          _ -> traverse (applyAssumptionsWorker assumptions') replaceIn
        )
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | PredicateExists var _ <- original = restrictAssumptions (inject var)
          | PredicateForall var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            (HashMap.filterWithKey (\term _ -> wouldNotCaptureTerm term) ***
            HashMap.filterWithKey (\predicate _ -> wouldNotCapture predicate))
            assumptions
          where
            wouldNotCapture = not . Predicate.hasFreeVariable variableName
            wouldNotCaptureTerm = not . TermLike.hasFreeVariable variableName

    applyAssumptionsWorkerTerm
        :: HashMap (TermLike variable) (TermLike variable)
        -> TermLike variable
        -> Changed (TermLike variable)
    applyAssumptionsWorkerTerm assumptions original
      | Just result <- HashMap.lookup original assumptions = Changed result

      | HashMap.null assumptions' = Unchanged original

      | otherwise =
        traverse (applyAssumptionsWorkerTerm assumptions') replaceIn
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | Exists_ _ var _ <- original = restrictAssumptions (inject var)
          | Forall_ _ var _ <- original = restrictAssumptions (inject var)
          | Mu_       var _ <- original = restrictAssumptions (inject var)
          | Nu_       var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            (HashMap.filterWithKey
                $ \termLike _ -> wouldNotCapture termLike)
                assumptions
          where
            wouldNotCapture = not . TermLike.hasFreeVariable variableName



{- | Get a local function definition from a 'TermLike'.

A local function definition is a predicate that we can use to evaluate a
function locally (based on the side conditions) when none of the functions
global definitions (axioms) apply. We are looking for a 'TermLike' of the form

@
\equals(f(...), C(...))
@

where @f@ is a function and @C@ is a constructor, sort injection or builtin.
@retractLocalFunction@ will match an @\equals@ predicate with its arguments
in either order, but the function pattern is always returned first in the
'Pair'.

 -}
retractLocalFunction
    :: TermLike variable
    -> Maybe (Pair (TermLike variable))
retractLocalFunction =
    \case
        Equals_ _ _ term1 term2 -> go term1 term2 <|> go term2 term1
        _ -> Nothing
  where
    go term1@(App_ symbol1 _) term2
      | isFunction symbol1 =
        case term2 of
            App_ symbol2 _
              | isConstructor symbol2 -> Just (Pair term1 term2)
            Inj_ _     -> Just (Pair term1 term2)
            Builtin_ _ -> Just (Pair term1 term2)
            _          -> Nothing
    go _ _ = Nothing

applyAndIdempotenceAndFindContradictions
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
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

splitIntoTermsAndNegations
    :: forall variable
    .  Ord variable
    => TermLike variable
    -> (Set (TermLike variable), Set (TermLike variable))
splitIntoTermsAndNegations =
    bimap Set.fromList Set.fromList
        . partitionWith termOrNegation
        . children
  where
    children :: TermLike variable -> [TermLike variable]
    children (And_ _ p1 p2) = children p1 ++ children p2
    children p = [p]

    -- Left is for regular terms, Right is negated terms
    termOrNegation
        :: TermLike variable
        -> Either (TermLike variable) (TermLike variable)
    termOrNegation t@(Not_ _ _) = Right t
    termOrNegation t            = Left t

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = partitionEithers . fmap f

{- | Simplify the conjunction (@\\and@) of two terms.

The comment for 'simplify' describes all the special cases handled by this.

-}
termAnd
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => HasCallStack
    => NotSimplifier (UnifierT simplifier)
    -> TermLike variable
    -> TermLike variable
    -> LogicT simplifier (Pattern variable)
termAnd notSimplifier p1 p2 =
    Logic.scatter
    =<< (lift . runUnifierT notSimplifier) (termAndWorker p1 p2)
  where
    termAndWorker
        :: TermLike variable
        -> TermLike variable
        -> UnifierT simplifier (Pattern variable)
    termAndWorker first second = do
        let maybeTermAnd' = maybeTermAnd notSimplifier termAndWorker first second
        patt <- runMaybeT maybeTermAnd'
        return $ fromMaybe andPattern patt
      where
        andPattern = Pattern.fromTermLike (mkAnd first second)
