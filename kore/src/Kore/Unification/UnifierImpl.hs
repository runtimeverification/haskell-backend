{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}
module Kore.Unification.UnifierImpl
    ( simplifyAnds
    , deduplicateSubstitution
    , normalizeOnce
    , normalizeExcept
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Monad
    ( foldM
    )
import qualified Data.Functor.Foldable as Recursive
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map

import qualified Branch
import Kore.Internal.Condition
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
    ( normalizeSubstitution
    )
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )
import qualified Kore.Unification.Unify as Unifier
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

simplifyAnds
    :: forall variable unifier
    .  SimplifierVariable variable
    => MonadUnify unifier
    => NonEmpty (TermLike variable)
    -> unifier (Pattern variable)
simplifyAnds (NonEmpty.sort -> patterns) = do
    result <- foldM simplifyAnds' Pattern.top patterns
    TopBottom.guardAgainstBottom result
    return result
  where
    simplifyAnds'
        :: Pattern variable
        -> TermLike variable
        -> unifier (Pattern variable)
    simplifyAnds' intermediate termLike =
        case Cofree.tailF (Recursive.project termLike) of
            AndF And { andFirst, andSecond } ->
                foldM simplifyAnds' intermediate [andFirst, andSecond]
            _ -> do
                unified <- termUnification intermediateTerm termLike
                normalizeExcept
                    $ Pattern.andCondition unified intermediateCondition
      where
        (intermediateTerm, intermediateCondition) =
            Pattern.splitTerm intermediate

deduplicateSubstitution
    ::  forall variable unifier
    .   SimplifierVariable variable
    =>  MonadUnify unifier
    =>  Substitution variable
    ->  unifier
            ( Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
deduplicateSubstitution =
    worker Predicate.makeTruePredicate_ . Substitution.toMultiMap
  where
    worker
        ::  Predicate variable
        ->  Map (UnifiedVariable variable) (NonEmpty (TermLike variable))
        ->  unifier
                ( Predicate variable
                , Map (UnifiedVariable variable) (TermLike variable)
                )
    worker predicate substitutions
      | Just deduplicated <- traverse getSingleton substitutions
      = return (predicate, deduplicated)

      | otherwise = do
        simplified <-
            collectConditions
            <$> traverse simplifyAnds substitutions
        let -- Substitutions de-duplicated by simplification.
            substitutions' = toMultiMap $ Conditional.term simplified
            -- New conditions produced by simplification.
            Conditional { predicate = predicate' } = simplified
            predicate'' =
                Predicate.makeAndPredicate predicate predicate'
            -- New substitutions produced by simplification.
            Conditional { substitution } = simplified
            substitutions'' =
                Map.unionWith (<>) substitutions'
                $ Substitution.toMultiMap substitution
        worker predicate'' substitutions''

    getSingleton (t :| []) = Just t
    getSingleton _         = Nothing

    toMultiMap :: Map key value -> Map key (NonEmpty value)
    toMultiMap = Map.map (:| [])

    collectConditions
        :: Map key (Conditional variable term)
        -> Conditional variable (Map key term)
    collectConditions = sequenceA

normalizeOnce
    :: forall unifier variable term
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Conditional variable term
    -> unifier (Conditional variable term)
normalizeOnce Conditional { term, predicate, substitution } = do
    -- The intermediate steps do not need to be checked for \bottom because we
    -- use guardAgainstBottom at the end.
    (deduplicatedPredicate, deduplicatedSubstitution) <-
        deduplicateSubstitution substitution

    normalized <- normalizeSubstitution' deduplicatedSubstitution
    let
        Conditional { substitution = normalizedSubstitution } = normalized
        Conditional { predicate = normalizedPredicate } = normalized

        mergedPredicate =
            Predicate.makeMultipleAndPredicate
                [predicate, deduplicatedPredicate, normalizedPredicate]

    TopBottom.guardAgainstBottom mergedPredicate
    return Conditional
        { term
        , predicate = mergedPredicate
        , substitution = normalizedSubstitution
        }
  where
    normalizeSubstitution' =
        either Unifier.throwSubstitutionError return . normalizeSubstitution

normalizeExcept
    :: forall unifier variable term
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Conditional variable term
    -> unifier (Conditional variable term)
normalizeExcept conditional = do
    normalized <- normalizeOnce conditional
    let (term, predicate') = Conditional.splitTerm normalized
    simplified <- Branch.alternate $ Simplifier.simplifyCondition predicate'
    return simplified { term }
