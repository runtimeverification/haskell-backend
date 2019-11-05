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

import Data.Map.Strict
    ( Map
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
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier
    ( MakeAnd (..)
    , SubstitutionSimplifier (..)
    , deduplicateSubstitution
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Unification.Error
import Kore.Unification.Substitution
    ( Normalization (..)
    , Substitution
    )
import Kore.Unification.SubstitutionNormalization
    ( normalize
    )
import Kore.Unification.Unify
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
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
        deduplicated <-
            deduplicateSubstitution
                unificationMakeAnd
                substitution
        OrCondition.fromCondition <$> normalize1 deduplicated

    normalizeSubstitution'
        :: forall variable
        .  SubstitutionVariable variable
        => Map (UnifiedVariable variable) (TermLike variable)
        -> unifier (Condition variable)
    normalizeSubstitution' =
        maybe bottom fromNormalization . normalize
      where
        bottom = return Condition.bottom
        fromNormalization normalization@Normalization { denormalized }
          | null denormalized =
            pure $ Condition.fromNormalizationSimplified normalization
          | otherwise =
            simplifiableCycle variables
          where
            (variables, _) = unzip denormalized

    simplifiableCycle variables =
        throwSubstitutionError (SimplifiableCycle variables)

    normalize1
        ::  forall variable
        .   SubstitutionVariable variable
        =>  ( Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
        ->  unifier (Condition variable)
    normalize1 (predicate, deduplicated) = do
        normalized <- normalizeSubstitution' deduplicated
        return $ Condition.fromPredicate predicate <> normalized

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        unified <- termUnification termLike1 termLike2
        BranchT.alternate
            $ Simplifier.simplifyCondition
            $ Pattern.andCondition unified condition
