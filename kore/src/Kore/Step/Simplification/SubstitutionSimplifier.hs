{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    , simplification
    , unification
    ) where

import Control.Error
    ( maybeT
    )
import Data.Function
    ( (&)
    )
import Data.Map.Strict
    ( Map
    )

import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import Kore.Unification.SubstitutionNormalization
    ( normalize
    , normalizeSubstitution
    )
import qualified Kore.Unification.UnifierImpl as Unifier
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Unifier
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
simplification :: MonadSimplify simplifier => SubstitutionSimplifier simplifier
simplification =
    SubstitutionSimplifier worker
  where
    worker substitution = maybeUnwrapSubstitution $ do
        deduplicated <-
            -- TODO (thomas.tuegel): If substitution de-duplication fails with a
            -- unification error, this will still discard the entire
            -- substitution into the predicate. Fortunately, that seems to be
            -- rare enough to discount for now.
            Unifier.deduplicateSubstitution substitution
            & Unifier.maybeUnifierT
        OrCondition.fromConditions <$> traverse normalize1 deduplicated
      where
        maybeUnwrapSubstitution =
            let unwrapped =
                    OrCondition.fromCondition
                    . Condition.fromPredicate
                    . Syntax.Predicate.markSimplified
                    -- TODO (thomas.tuegel): Promoting the entire substitution
                    -- to the predicate is a problem. We should only promote the
                    -- part which has cyclic dependencies.
                    $ Syntax.Predicate.fromSubstitution substitution
            in maybeT (return unwrapped) return

    normalize1 (predicate, substitutions) = do
        let normalized =
                maybe Condition.bottom Condition.fromNormalization
                $ normalize substitutions
        return $ Condition.fromPredicate predicate <> normalized

{- | A 'SubstitutionSimplifier' to use during unification.

If the 'Substitution' cannot be normalized, this simplifier uses
'Unifier.throwSubstitutionError'.

 -}
unification
    :: forall unifier
    .  MonadUnify unifier
    => SubstitutionSimplifier unifier
unification =
    SubstitutionSimplifier worker
  where
    worker
        :: forall variable
        .  SubstitutionVariable variable
        => Substitution variable
        -> unifier (OrCondition variable)
    worker substitution =
        fmap OrCondition.fromConditions . Unifier.gather $ do
            deduplicated <- Unifier.deduplicateSubstitution substitution
            normalize1 deduplicated

    normalizeSubstitution'
        :: forall variable
        .  SubstitutionVariable variable
        => Map (UnifiedVariable variable) (TermLike variable)
        -> unifier (Condition variable)
    normalizeSubstitution' =
        either Unifier.throwSubstitutionError return . normalizeSubstitution

    normalize1
        ::  forall variable
        .   SubstitutionVariable variable
        =>  ( Syntax.Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
        ->  unifier (Condition variable)
    normalize1 (predicate, deduplicated) = do
        normalized <- normalizeSubstitution' deduplicated
        return $ Condition.fromPredicate predicate <> normalized
