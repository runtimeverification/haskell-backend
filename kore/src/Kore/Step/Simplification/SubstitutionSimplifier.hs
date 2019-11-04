{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    , simplification
    , MakeAnd (..)
    , deduplicateSubstitution
    , simplifyAnds
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Monad
    ( foldM
    )
import Data.Function
    ( (&)
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

import Branch
    ( BranchT
    )
import qualified Branch
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( And (..)
    , pattern And_
    , TermLike
    , TermLikeF (..)
    , mkAnd
    , mkVar
    )
import Kore.Predicate.Predicate
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , simplifyConditionalTerm
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
    ( normalize
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

newtype SubstitutionSimplifier simplifier =
    SubstitutionSimplifier
        { simplifySubstitution
            :: forall variable
            .  SubstitutionVariable variable
            => Substitution variable
            -> simplifier (OrCondition variable)
        }

{- | A 'SubstitutionSimplifier' to use during simplification.

If the 'Substitution' cannot be normalized, this simplifier moves the
denormalized part into the predicate, but returns the normalized part as a
substitution.

 -}
simplification
    :: forall simplifier
    .  MonadSimplify simplifier
    => SubstitutionSimplifier simplifier
simplification =
    SubstitutionSimplifier { simplifySubstitution }
  where
    makeAnd' = simplifierMakeAnd
    simplifySubstitution
        :: forall variable
        .  SubstitutionVariable variable
        => Substitution variable
        -> simplifier (OrCondition variable)
    simplifySubstitution substitution = do
        deduplicated <-
            -- TODO (thomas.tuegel): If substitution de-duplication fails with a
            -- unification error, this will still discard the entire
            -- substitution into the predicate. Fortunately, that seems to be
            -- rare enough to discount for now.
            deduplicateSubstitution makeAnd' substitution
            & Branch.gather
        OrCondition.fromConditions
            <$> traverse (normalize1 . promoteUnsimplified) deduplicated

    isAnd (And_ _ _ _) = True
    isAnd _            = False

    promoteUnsimplified (predicate, substitutions) =
        let (unsimplified, simplified) = Map.partition isAnd substitutions
            predicate' =
                Predicate.makeMultipleAndPredicate
                . (:) predicate
                . map mkUnsimplified
                $ Map.toList unsimplified
            mkUnsimplified (mkVar -> variable, termLike) =
                Predicate.makeEqualsPredicate variable termLike
        in (predicate', simplified)

    normalize1 (predicate, substitutions) = do
        let normalized =
                maybe Condition.bottom Condition.fromNormalizationSimplified
                $ normalize substitutions
        return $ Condition.fromPredicate predicate <> normalized

-- | Interface for constructing a simplified 'And' pattern.
newtype MakeAnd monad =
    MakeAnd
        { makeAnd
            :: forall variable
            .  SubstitutionVariable variable
            => TermLike variable
            -> TermLike variable
            -> Condition variable
            -> monad (Pattern variable)
            -- ^ Construct a simplified 'And' pattern of two 'TermLike's under
            -- the given 'Predicate.Predicate'.
        }

simplifierMakeAnd :: MonadSimplify simplifier => MakeAnd (BranchT simplifier)
simplifierMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        simplified <-
            mkAnd termLike1 termLike2
            & simplifyConditionalTerm condition
        TopBottom.guardAgainstBottom simplified
        return simplified

simplifyAnds
    ::  forall variable monad
    .   ( SubstitutionVariable variable
        , Monad monad
        )
    => MakeAnd monad
    -> NonEmpty (TermLike variable)
    -> monad (Pattern variable)
simplifyAnds MakeAnd { makeAnd } (NonEmpty.sort -> patterns) = do
    foldM simplifyAnds' Pattern.top patterns
  where
    simplifyAnds'
        :: Pattern variable
        -> TermLike variable
        -> monad (Pattern variable)
    simplifyAnds' intermediate termLike =
        case Cofree.tailF (Recursive.project termLike) of
            AndF And { andFirst, andSecond } ->
                foldM simplifyAnds' intermediate [andFirst, andSecond]
            _ -> do
                simplified <-
                    makeAnd
                        intermediateTerm
                        termLike
                        intermediateCondition
                return (Pattern.andCondition simplified intermediateCondition)
      where
        (intermediateTerm, intermediateCondition) =
            Pattern.splitTerm intermediate

deduplicateSubstitution
    :: forall variable monad
    .   ( SubstitutionVariable variable
        , Monad monad
        )
    =>  MakeAnd monad
    ->  Substitution variable
    ->  monad
            ( Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
deduplicateSubstitution makeAnd' =
    worker Predicate.makeTruePredicate . Substitution.toMultiMap
  where
    simplifyAnds' = simplifyAnds makeAnd'
    worker
        ::  Predicate variable
        ->  Map (UnifiedVariable variable) (NonEmpty (TermLike variable))
        ->  monad
                ( Predicate variable
                , Map (UnifiedVariable variable) (TermLike variable)
                )
    worker predicate substitutions
      | Just deduplicated <- traverse getSingleton substitutions
      = return (predicate, deduplicated)

      | otherwise = do
        simplified <- collectConditions <$> traverse simplifyAnds' substitutions
        let -- Substitutions de-duplicated by simplification.
            substitutions' = toMultiMap $ Conditional.term simplified
            -- New conditions produced by simplification.
            Conditional { predicate = predicate' } = simplified
            predicate'' = Predicate.makeAndPredicate predicate predicate'
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
