{-|
Module      : Kore.Step.Simplification.And
Description : Tools for And pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.And
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    , simplifyEvaluatedMultiple
    , And (..)
    , termAnd
    ) where

import Prelude.Kore

import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import Control.Error
    ( fromMaybe
    , runMaybeT
    )
import Control.Monad
    ( foldM
    )
import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.State.Strict as State
import Data.Bifunctor
    ( bimap
    )
import Data.Either
    ( partitionEithers
    )
import qualified Data.Functor.Foldable as Recursive
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.List
    ( foldl'
    , foldl1'
    , sortBy
    )
import qualified Data.List as List
    ( sort
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Traversable
    ( for
    )

import Branch
import qualified Branch as BranchT
import Changed
import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.Error
    ( printError
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , getMultiAndPredicate
    , makeAndPredicate
    , makePredicate
    , makeTruePredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
    ( depth
    , setSimplified
    , simplifiedAttribute
    , unwrapPredicate
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( And (..)
    , pattern And_
    , pattern Exists_
    , pattern Forall_
    , InternalVariable
    , pattern Mu_
    , pattern Not_
    , pattern Nu_
    , Sort
    , TermLike
    , mkAnd
    , mkBottom
    , mkBottom_
    , mkNot
    , mkTop
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
    ( hasFreeVariable
    , setSimplified
    , simplifiedAttribute
    )
import Kore.Step.Simplification.AndTerms
    ( maybeTermAnd
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Substitution as Substitution
import Kore.Unification.UnifierT
    ( runUnifierT
    )
import Kore.Unification.Unify
    ( MonadUnify
    )
import Kore.Unparser
    ( unparseToString
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (ElemVar, SetVar)
    )

{-|'simplify' simplifies an 'And' of 'OrPattern'.

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
    :: (InternalVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> And Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify sideCondition And { andFirst = first, andSecond = second } =
    simplifyEvaluated sideCondition first second

{-| simplifies an And given its two 'OrPattern' children.

See 'simplify' for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (And Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually
cache information besides the pattern sort, which will make it even more useful
to carry around.

-}
simplifyEvaluated
    :: (InternalVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> OrPattern variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated sideCondition first second
  | OrPattern.isFalse first  = return OrPattern.bottom
  | OrPattern.isFalse second = return OrPattern.bottom
  | OrPattern.isTrue first   = return second
  | OrPattern.isTrue second  = return first
  | otherwise                = do
    result <-
        gather $ do
            first1 <- scatter first
            second1 <- scatter second
            makeEvaluate sideCondition first1 second1
    return (OrPattern.fromPatterns result)

simplifyEvaluatedMultiple
    :: (InternalVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> [OrPattern variable]
    -> simplifier (OrPattern variable)
simplifyEvaluatedMultiple _ [] = return OrPattern.top
simplifyEvaluatedMultiple sideCondition (pat : patterns) =
    foldM (simplifyEvaluated sideCondition) pat patterns

{-|'makeEvaluate' simplifies an 'And' of 'Pattern's.

See the comment for 'simplify' to find more details.
-}
makeEvaluate
    ::  ( InternalVariable variable
        , HasCallStack
        , MonadSimplify simplifier
        )
    => SideCondition variable
    -> Pattern variable
    -> Pattern variable
    -> BranchT simplifier (Pattern variable)
makeEvaluate sideCondition first second
  | Pattern.isBottom first || Pattern.isBottom second = empty
  | Pattern.isTop first = return second
  | Pattern.isTop second = return first
  | otherwise = makeEvaluateNonBool sideCondition first second

makeEvaluateNonBool
    ::  ( InternalVariable variable
        , HasCallStack
        , MonadSimplify simplifier
        )
    => SideCondition variable
    -> Pattern variable
    -> Pattern variable
    -> BranchT simplifier (Pattern variable)
makeEvaluateNonBool
    sideCondition
    first@Conditional { term = firstTerm }
    second@Conditional { term = secondTerm }
  = do
    terms <- termAnd firstTerm secondTerm
    let firstCondition = Conditional.withoutTerm first
        secondCondition = Conditional.withoutTerm second
        initialConditions = firstCondition <> secondCondition
        merged = Conditional.andCondition terms initialConditions
    normalized <- Substitution.normalize sideCondition merged
    let normalizedPredicates =
            applyAndIdempotenceAndFindContradictions
                (Conditional.term normalized)
        normalizedPredicate =
            promoteSubTermsToTop (Conditional.predicate normalized)
    case normalizedPredicate of
        Unchanged unchanged ->
            return normalized
                { term = normalizedPredicates
                , predicate = unchanged
                }
        Changed changed ->
            simplifyCondition
                sideCondition
                normalized
                    { term = normalizedPredicates
                    , predicate = changed
                    }

promoteSubTermsToTop
    :: forall variable
    .  InternalVariable variable
    => Predicate variable
    -> Changed (Predicate variable)
promoteSubTermsToTop predicate =
    case normalizedPredicates of
        Unchanged unchanged -> Unchanged $
            foldl'
                makeSimplifiedAndPredicate
                makeTruePredicate_
                (List.sort unchanged)
        Changed changed -> Changed $
            foldl' makeAndPredicate makeTruePredicate_ changed
  where
    andPredicates :: [Predicate variable]
    andPredicates = getMultiAndPredicate predicate

    sortedAndPredicates :: [Predicate variable]
    sortedAndPredicates = sortByDepth andPredicates

    sortByDepth :: [Predicate variable] -> [Predicate variable]
    sortByDepth = sortBy (compare `on` Predicate.depth)

    normalizedPredicates :: Changed [Predicate variable]
    normalizedPredicates =
        flip evalStateT HashMap.empty
        $ for sortedAndPredicates
        $ \predicate' -> do
            let original = Predicate.unwrapPredicate predicate'
            result <- replaceWithTopNormalized original
            insertAssumption result
            return result

    insertAssumption
        :: Predicate variable
        -> StateT (HashMap (TermLike variable) (TermLike variable)) Changed ()
    insertAssumption predicate1 =
        State.modify' insert
      where
        insert =
            case termLike of
                -- Infer that the predicate is \bottom.
                Not_ _ notChild -> HashMap.insert notChild (mkBottom sort)
                -- Infer that the predicate is \top.
                _               -> HashMap.insert termLike (mkTop    sort)
        termLike = Predicate.unwrapPredicate predicate1
        sort = termLikeSort termLike

    replaceWithTopNormalized
        ::  TermLike variable
        ->  StateT (HashMap (TermLike variable) (TermLike variable)) Changed
                (Predicate variable)
    replaceWithTopNormalized replaceIn = do
        replacements <- State.get
        lift $ fmap
            (unsafeMakePredicate replacements replaceIn)
            (replaceWithTop replacements replaceIn)

    unsafeMakePredicate replacements original result =
        case makePredicate result of
            -- TODO (ttuegel): https://github.com/kframework/kore/issues/1442
            -- should make it impossible to have an error here.
            Left err -> error $ unlines
                [ "Replacing"
                , unlines $ map unparseToString $ HashMap.keys replacements
                , "in"
                , unparseToString original
                , "did not produce a predicate!"
                , printError err
                ]
            Right p -> p

    replaceWithTop
        :: HashMap (TermLike variable) (TermLike variable)
        -> TermLike variable
        -> Changed (TermLike variable)
    replaceWithTop replacements original
      | Just result <- HashMap.lookup original replacements = Changed result

      | HashMap.null replacements' = Unchanged original

      | otherwise =
        traverse (replaceWithTop replacements') replaceIn
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        replacements'
          | Exists_ _ var _ <- original = restrictReplacements (ElemVar var)
          | Forall_ _ var _ <- original = restrictReplacements (ElemVar var)
          | Mu_       var _ <- original = restrictReplacements (SetVar  var)
          | Nu_       var _ <- original = restrictReplacements (SetVar  var)
          | otherwise = replacements

        restrictReplacements unifiedVariable =
            HashMap.filterWithKey
                (\termLike _ -> wouldNotCapture termLike)
                replacements
          where
            wouldNotCapture = not . TermLike.hasFreeVariable unifiedVariable

    makeSimplifiedAndPredicate a b =
        Predicate.setSimplified
            (on (<>) Predicate.simplifiedAttribute a b)
            (makeAndPredicate a b)

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
    .  (InternalVariable variable, MonadSimplify simplifier)
    => HasCallStack
    => TermLike variable
    -> TermLike variable
    -> BranchT simplifier (Pattern variable)
termAnd p1 p2 =
    either (const andTerm) BranchT.scatter
    =<< (lift . runUnifierT) (termAndWorker p1 p2)
  where
    andTerm = return $ Pattern.fromTermLike (mkAnd p1 p2)
    termAndWorker
        :: MonadUnify unifier
        => TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termAndWorker first second = do
        let maybeTermAnd' = maybeTermAnd termAndWorker first second
        patt <- runMaybeT maybeTermAnd'
        return $ fromMaybe andPattern patt
      where
        andPattern = Pattern.fromTermLike (mkAnd first second)
