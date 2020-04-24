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

import Prelude.Kore

import Control.Error
    ( MaybeT
    , maybeT
    )
import Control.Monad.Trans.Identity
    ( IdentityT (..)
    )

import qualified Branch as BranchT
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.Substitution
    ( Normalization
    , Substitution
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import Kore.Step.Simplification.NotSimplifier
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier
    ( MakeAnd (..)
    , SubstitutionSimplifier (..)
    , deduplicateSubstitution
    , simplifySubstitutionWorker
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Unify

{- | A 'SubstitutionSimplifier' to use during unification.

If multiple assignments to a single variable cannot be unified, this simplifier
uses 'Unifier.throwUnificationError'.

 -}
substitutionSimplifier
    :: forall unifier
    .  MonadUnify unifier
    => SubstitutionSimplifier unifier unifier
substitutionSimplifier =
    SubstitutionSimplifier wrapper
  where
    wrapper
        :: forall variable
        .  InternalVariable variable
        => NotSimplifier unifier
        -> SideCondition variable
        -> Substitution variable
        -> unifier (OrCondition variable)
    wrapper notSimplifier sideCondition substitution = do
        (predicate, result) <-
            worker substitution
            & maybeT empty return
        let condition = Condition.fromNormalizationSimplified result
        let condition' = Condition.fromPredicate predicate <> condition
            conditions = OrCondition.fromCondition condition'
        TopBottom.guardAgainstBottom conditions
        return conditions
      where
        worker
            :: Substitution variable
            -> MaybeT
                unifier
                (Predicate variable, Normalization variable)
        worker = simplifySubstitutionWorker notSimplifier sideCondition unificationMakeAnd

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd notSimplifier termLike1 termLike2 sideCondition = do
        unified <- termUnification notSimplifier termLike1 termLike2
        Simplifier.simplifyCondition notSimplifier sideCondition unified
            & BranchT.alternate
