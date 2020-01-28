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

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( maybeT
    )
import Data.Function
    ( (&)
    )

import qualified Branch as BranchT
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.SideCondition as SideCondition
    ( topTODO
    )
import Kore.Internal.Substitution
    ( Normalization (..)
    , Substitution
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier
    ( MakeAnd (..)
    , SubstitutionSimplifier (..)
    , deduplicateSubstitution
    , simplifySubstitutionWorker
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Error
import Kore.Unification.Unify

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
        (predicate, result) <- worker substitution & maybeT empty return
        condition <- fromNormalization result
        let condition' = Condition.fromPredicate predicate <> condition
            conditions = OrCondition.fromCondition condition'
        TopBottom.guardAgainstBottom conditions
        return conditions
      where
        worker =
            simplifySubstitutionWorker SideCondition.topTODO unificationMakeAnd

    fromNormalization
        :: SimplifierVariable variable
        => Normalization variable
        -> unifier (Condition variable)
    fromNormalization normalization@Normalization { denormalized }
      | null denormalized =
        return (Condition.fromNormalizationSimplified normalization)
      | otherwise =
        simplifiableCycle
      where
        simplifiableCycle =
            throwSubstitutionError $ SimplifiableCycle variables normalization
          where
            (variables, _) = unzip denormalized

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 sideCondition = do
        unified <- termUnification termLike1 termLike2
        Simplifier.simplifyCondition sideCondition unified
            & BranchT.alternate
