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
import qualified Control.Exception as Exception
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
    SubstitutionSimplifier wrapper
  where
    wrapper
        :: forall variable
        .  SubstitutionVariable variable
        => Substitution variable
        -> unifier (OrCondition variable)
    wrapper substitution = do
        (predicate, result) <- simplifySubstitutionWorker substitution
        condition <- maybe empty fromNormalization result
        let condition' = Condition.fromPredicate predicate <> condition
            conditions = OrCondition.fromCondition condition'
        TopBottom.guardAgainstBottom conditions
        return conditions

    fromNormalization
        :: SimplifierVariable variable
        => Normalization variable
        -> unifier (Condition variable)
    fromNormalization normalization@Normalization { denormalized }
      | null denormalized =
        return (Condition.fromNormalizationSimplified normalization)
      | otherwise =
        simplifiableCycle denormalized

    simplifiableCycle
        :: SimplifierVariable variable
        => UnwrappedSubstitution variable
        -> unifier a
    simplifiableCycle denorm =
        throwSubstitutionError (SimplifiableCycle variables)
      where
        (variables, _) = unzip denorm

simplifySubstitutionWorker
    :: forall variable unifier
    .  SubstitutionVariable variable
    => MonadUnify unifier
    => Substitution variable
    -> unifier (Predicate variable, Maybe (Normalization variable))
simplifySubstitutionWorker = \substitution -> do
    (result, Private { accum = condition }) <-
        runStateT loop Private
            { count = maxBound
            , accum = Condition.fromSubstitution substitution
            }
    (assertNullSubstitution condition . return)
        (Condition.predicate condition, result)
  where
    assertNullSubstitution =
        Exception.assert . Substitution.null . Condition.substitution

    loop :: StateT (Private variable) unifier (Maybe (Normalization variable))
    loop = do
        simplified <-
            takeSubstitution
            >>= deduplicate
            >>= return . Substitution.normalize
            >>= traverse simplifyNormalizationOnce
        substitution <- takeSubstitution
        lastCount <- Lens.use (field @"count")
        case simplified of
            Just normalization@Normalization { denormalized }
              | not fullySimplified, makingProgress -> do
                Lens.assign (field @"count") thisCount
                addSubstitution substitution
                addSubstitution $ Substitution.wrapNormalization normalization
                loop
                where
                fullySimplified =
                    null denormalized && Substitution.null substitution
                makingProgress =
                    thisCount < lastCount || null denormalized
                thisCount = length denormalized
            _ -> return simplified

    simplifyNormalizationOnce
        ::  SubstitutionVariable variable
        =>  MonadSimplify simplifier
        =>  Normalization variable
        ->  StateT (Private variable) simplifier (Normalization variable)
    simplifyNormalizationOnce =
        return
        >=> simplifyNormalized
        >=> return . Substitution.applyNormalized
        >=> simplifyDenormalized

    simplifyNormalized
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => Normalization variable
        -> StateT (Private variable) simplifier (Normalization variable)
    simplifyNormalized =
        Lens.traverseOf
            (field @"normalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifyDenormalized
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => Normalization variable
        -> StateT (Private variable) simplifier (Normalization variable)
    simplifyDenormalized =
        Lens.traverseOf
            (field @"denormalized" . Lens.traversed)
            simplifySingleSubstitution

    simplifySingleSubstitution
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => SingleSubstitution variable
        -> StateT (Private variable) simplifier (SingleSubstitution variable)
    simplifySingleSubstitution subst@(uVar, _) =
        case uVar of
            SetVar _ -> return subst
            ElemVar _ -> traverse simplifyTermLike subst

    simplifyTermLike
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => TermLike variable
        -> StateT (Private variable) simplifier (TermLike variable)
    simplifyTermLike termLike = do
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
