{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Unification.SubstitutionSimplifier
    ( substitutionSimplifier
    , unificationMakeAnd
    -- * Re-exports
    , module Kore.Step.Simplification.SubstitutionSimplifier
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Category
    ( (>>>)
    )
import Control.Lens
    ( (<>=)
    )
import qualified Control.Lens as Lens
import Control.Monad
    ( (>=>)
    )
import Control.Monad.State.Strict
    ( MonadState
    , StateT
    , runStateT
    )
import qualified Control.Monad.Trans as Trans
import Data.Function
    ( (&)
    )
import Data.Generics.Product.Fields
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified GHC.Generics as GHC

import qualified Branch as BranchT
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( Predicate
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier
    ( MakeAnd (..)
    , SubstitutionSimplifier (..)
    , deduplicateSubstitution
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Error
import Kore.Unification.Substitution
    ( Normalization (..)
    , SingleSubstitution
    , Substitution
    , UnwrappedSubstitution
    )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.SubstitutionNormalization as Substitution
    ( normalize
    )
import Kore.Unification.Unify
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

{- | A 'SubstitutionSimplifier' to use during unification.

If the 'Substitution' cannot be normalized, this simplifier uses
'Unifier.throwSubstitutionError'.

 -}
substitutionSimplifier
    :: forall unifier
    .  MonadUnify unifier
    => SubstitutionSimplifier unifier
substitutionSimplifier =
    SubstitutionSimplifier worker
  where
    worker
        :: forall variable
        .  SubstitutionVariable variable
        => Substitution variable
        -> unifier (OrCondition variable)
    worker substitution = do
        (result, Private { accum = condition }) <- loop & flip runStateT private
        case result of
            Nothing -> empty
            Just normalization@Normalization { denormalized }
              | null denormalized -> do
                let normalizationCondition =
                        Condition.fromNormalizationSimplified normalization
                    conditions =
                        OrCondition.fromCondition
                        $ condition <> normalizationCondition
                TopBottom.guardAgainstBottom conditions
                return conditions
              | otherwise ->
                simplifiableCycle denormalized
      where
        private =
            Private
                { count = maxBound
                , accum = Condition.fromSubstitution substitution
                }

    loop
        ::  forall variable
        .   SubstitutionVariable variable
        =>  StateT (Private variable) unifier (Maybe (Normalization variable))
    loop = do
        simplified <-
            takeSubstitution
            >>= deduplicate
            >>= (Substitution.normalize >>> traverse simplifyNormalization)
        substitution <- takeSubstitution
        lastCount <- Lens.use (field @"count")
        case simplified of
            Nothing -> do
                return simplified
            Just normalization@Normalization { denormalized }
              | null denormalized, Substitution.null substitution -> do
                return simplified
              | thisCount >= lastCount, thisCount /= 0 ->
                return simplified
              | otherwise -> do
                Lens.assign (field @"count") thisCount
                addSubstitution substitution
                addSubstitution $ Substitution.wrapNormalization normalization
                loop
              where
                thisCount = length denormalized

    simplifyNormalization
        ::  forall variable
        .   SubstitutionVariable variable
        =>  Normalization variable
        ->  StateT (Private variable) unifier (Normalization variable)
    simplifyNormalization =
        return
        >=> simplifyNormalized
        >=> return . applyNormalized
        >=> simplifyDenormalized

    simplifyNormalized
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => Normalization variable
        -> StateT (Private variable) simplifier (Normalization variable)
    simplifyNormalized =
        Lens.traverseOf (field @"normalized" . Lens.traversed) simplify

    simplifyDenormalized
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => Normalization variable
        -> StateT (Private variable) simplifier (Normalization variable)
    simplifyDenormalized =
        Lens.traverseOf (field @"denormalized" . Lens.traversed) simplify

    applyNormalized
        :: SubstitutionVariable variable
        => Normalization variable
        -> Normalization variable
    applyNormalized Normalization { normalized, denormalized } =
        Normalization
            { normalized
            , denormalized = (fmap . fmap) substitute denormalized
            }
      where
        substitute = TermLike.substitute (Map.fromList normalized)

    simplify
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => SingleSubstitution variable
        -> StateT (Private variable) simplifier (SingleSubstitution variable)
    simplify subst@(uVar, _) =
        case uVar of
            SetVar _ -> return subst
            ElemVar _ -> traverse simplify1 subst

    simplify1
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => TermLike variable
        -> StateT (Private variable) simplifier (TermLike variable)
    simplify1 termLike = do
        orPattern <- Simplifier.simplifyTerm termLike
        case OrPattern.toPatterns orPattern of
            [        ] -> do
                addCondition Condition.bottom
                return termLike
            [pattern1] -> do
                let (termLike1, condition) = Pattern.splitTerm pattern1
                addCondition condition
                return termLike1
            _          -> return termLike

    deduplicate
        ::  SimplifierVariable variable
        =>  Substitution variable
        ->  StateT (Private variable) unifier
                (Map (UnifiedVariable variable) (TermLike variable))
    deduplicate substitution = do
        (predicate, substitution') <-
            deduplicateSubstitution unificationMakeAnd substitution
            & Trans.lift
        addPredicate predicate
        return substitution'

    simplifiableCycle
        :: SimplifierVariable variable
        => UnwrappedSubstitution variable
        -> unifier a
    simplifiableCycle denorm =
        throwSubstitutionError (SimplifiableCycle variables)
      where
        (variables, _) = unzip denorm

data Private variable =
    Private
        { accum :: !(Condition variable)
        -- ^ The current condition, accumulated during simplification.
        , count :: !Int
        -- ^ The current number of denormalized substitutions.
        }
    deriving (GHC.Generic)

addCondition
    :: SimplifierVariable variable
    => MonadState (Private variable) state
    => Condition variable
    -> state ()
addCondition condition = field @"accum" <>= condition

addPredicate
    :: SimplifierVariable variable
    => MonadState (Private variable) state
    => Predicate variable
    -> state ()
addPredicate = addCondition . Condition.fromPredicate

addSubstitution
    :: SimplifierVariable variable
    => MonadState (Private variable) state
    => Substitution variable
    -> state ()
addSubstitution = addCondition . Condition.fromSubstitution

takeSubstitution
    :: SimplifierVariable variable
    => MonadState (Private variable) state
    => state (Substitution variable)
takeSubstitution = do
    substitution <- Lens.use (field @"accum".field @"substitution")
    Lens.assign (field @"accum".field @"substitution") mempty
    return substitution

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        unified <- termUnification termLike1 termLike2
        BranchT.alternate
            $ Simplifier.simplifyCondition
            $ Pattern.andCondition unified condition
