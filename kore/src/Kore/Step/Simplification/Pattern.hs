{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplifyTopConfiguration
    , simplify
    ) where

import Prelude.Kore

import Control.Monad.State.Strict
    ( State
    , evalState
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.List
    ( sortOn
    )
import Data.Traversable
    ( for
    )

import Kore.Attribute.Synthetic
    ( synthesize
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( andCondition
    , topTODO
    )
import Kore.Internal.Substitution
    ( toMap
    )
import Kore.Internal.Symbol
    ( isConstructor
    , isFunction
    )
import Kore.Internal.TermLike
    ( pattern App_
    , pattern Equals_
    , pattern Exists_
    , pattern Forall_
    , pattern Mu_
    , pattern Not_
    , pattern Nu_
    , TermLike
    , Variable (..)
    , mkBottom
    , mkTop
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    , simplifyCondition
    , simplifyConditionalTerm
    )
import Kore.Substitute
    ( substitute
    )
import Kore.Unparser
    ( unparse
    )

import Pair
import qualified Pretty

{-| Simplifies the pattern without a side-condition (i.e. it's top)
and removes the exists quantifiers at the top.
-}
simplifyTopConfiguration
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => Pattern variable
    -> simplifier (OrPattern variable)
simplifyTopConfiguration patt = do
    simplified <- simplify SideCondition.topTODO patt
    return (OrPattern.map removeTopExists simplified)
  where
    removeTopExists :: Pattern variable -> Pattern variable
    removeTopExists p@Conditional{ term = Exists_ _ _ quantified } =
        removeTopExists p {term = quantified}
    removeTopExists p = p

{-| Simplifies an 'Pattern', returning an 'OrPattern'.
-}
simplify
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
simplify sideCondition pattern' =
    OrPattern.observeAllT $ do
        withSimplifiedCondition <-
            simplifyCondition
                sideCondition
                (simplifyConjunctions pattern')
        let (term, simplifiedCondition) =
                Conditional.splitTerm withSimplifiedCondition
            term' = substitute (toMap $ substitution simplifiedCondition) term
            termSideCondition =
                sideCondition `SideCondition.andCondition` simplifiedCondition
        simplifiedTerm <- simplifyConditionalTerm termSideCondition term'
        let simplifiedPattern =
                Conditional.andCondition simplifiedTerm simplifiedCondition
        simplifyCondition
            sideCondition
            (simplifyConjunctions simplifiedPattern)
  where
    simplifyConjunctions patt =
        let predicates = MultiAnd.fromPredicate . predicate $ patt
            newPredicate =
                MultiAnd.toPredicate
                $ simplifyConjunctionByAssumption predicates
         in Pattern.withCondition
                (term patt)
                (from (substitution patt) <> from newPredicate)

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
    -> MultiAnd (Predicate variable)
simplifyConjunctionByAssumption (Foldable.toList -> andPredicates) =
    MultiAnd.make
    $ flip evalState HashMap.empty
    $ for (sortBySize andPredicates)
    $ \predicate' -> do
        let original = Predicate.unwrapPredicate predicate'
        result <- applyAssumptions original
        assume result
        return result
  where
    -- Sorting by size ensures that every clause is considered before any clause
    -- which could contain it, because the containing clause is necessarily
    -- larger.
    sortBySize :: [Predicate variable] -> [Predicate variable]
    sortBySize = sortOn (size . from)

    size :: TermLike variable -> Int
    size =
        Recursive.fold $ \(_ :< termLikeF) ->
            case termLikeF of
                TermLike.EvaluatedF evaluated -> TermLike.getEvaluated evaluated
                TermLike.DefinedF defined -> TermLike.getDefined defined
                _ -> 1 + Foldable.sum termLikeF

    assume
        :: Predicate variable
        -> State (HashMap (TermLike variable) (TermLike variable)) ()
    assume predicate1 =
        State.modify' (assumeEqualTerms . assumePredicate)
      where
        assumePredicate =
            case termLike of
                Not_ _ notChild ->
                    -- Infer that the predicate is \bottom.
                    HashMap.insert notChild (mkBottom sort)
                _ ->
                    -- Infer that the predicate is \top.
                    HashMap.insert termLike (mkTop sort)
        assumeEqualTerms =
            case retractLocalFunction termLike of
                Just (Pair term1 term2) -> HashMap.insert term1 term2
                _ -> id

        termLike = Predicate.unwrapPredicate predicate1
        sort = termLikeSort termLike

    applyAssumptions
        ::  TermLike variable
        ->  State
                (HashMap (TermLike variable) (TermLike variable))
                (Predicate variable)
    applyAssumptions replaceIn = do
        assumptions <- State.get
        unsafeMakePredicate
            assumptions
            replaceIn
            (applyAssumptionsWorker assumptions replaceIn)
            & return

    unsafeMakePredicate replacements original result =
        case makePredicate result of
            -- TODO (ttuegel): https://github.com/kframework/kore/issues/1442
            -- should make it impossible to have an error here.
            Left err ->
                (error . show . Pretty.vsep . map (either id (Pretty.indent 4)))
                [ Left "Replacing"
                , Right (Pretty.vsep (unparse <$> HashMap.keys replacements))
                , Left "in"
                , Right (unparse original)
                , Right (Pretty.pretty err)
                ]
            Right p -> p

    applyAssumptionsWorker
        :: HashMap (TermLike variable) (TermLike variable)
        -> TermLike variable
        -> TermLike variable
    applyAssumptionsWorker assumptions original
      | Just result <- HashMap.lookup original assumptions = result

      | HashMap.null assumptions' = original

      | otherwise =
        fmap (applyAssumptionsWorker assumptions') replaceIn
        & synthesize

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | Exists_ _ var _ <- original = restrictAssumptions (inject var)
          | Forall_ _ var _ <- original = restrictAssumptions (inject var)
          | Mu_       var _ <- original = restrictAssumptions (inject var)
          | Nu_       var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            HashMap.filterWithKey
                (\termLike _ -> wouldNotCapture termLike)
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

where @f@ is a function and @C@ is a constructor. @retractLocalFunction@ will
match an @\equals@ predicate with its arguments in either order, but the
function pattern is always returned first in the 'Pair'.

 -}
retractLocalFunction
    :: TermLike variable
    -> Maybe (Pair (TermLike variable))
retractLocalFunction (Equals_ _ _ term1@(App_ symbol1 _) term2@(App_ symbol2 _))
  | isConstructor symbol1, isFunction symbol2 = Just (Pair term2 term1)
  | isConstructor symbol2, isFunction symbol1 = Just (Pair term1 term2)
retractLocalFunction _ = Nothing
