{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    , simplification
    , unification
    , original
    ) where

import Control.Error
    ( MaybeT
    , maybeT
    )
import Data.Function
    ( (&)
    )
import Data.Map.Strict
    ( Map
    )

import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
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
            -> simplifier (OrPredicate variable)
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
    worker substitution = maybeUnwrapSubstitution substitution $ do
        deduplicated <-
            -- TODO (thomas.tuegel): If substitution de-duplication fails with a
            -- unification error, this will still discard the entire
            -- substitution into the predicate. Fortunately, that seems to be
            -- rare enough to discount for now.
            Unifier.deduplicateSubstitution substitution
            & Unifier.maybeUnifierT
        OrPredicate.fromPredicates <$> traverse normalize1 deduplicated

    normalize1 (predicate, substitutions) = do
        let normalized =
                maybe Predicate.bottom Predicate.fromNormalization
                $ normalize substitutions
        return $ Predicate.fromPredicate predicate <> normalized

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
        -> unifier (OrPredicate variable)
    worker substitution =
        fmap OrPredicate.fromPredicates . Unifier.gather $ do
            deduplicated <- Unifier.deduplicateSubstitution substitution
            normalize1 deduplicated

    normalizeSubstitution'
        :: forall variable
        .  SubstitutionVariable variable
        => Map (UnifiedVariable variable) (TermLike variable)
        -> unifier (Predicate variable)
    normalizeSubstitution' =
        either Unifier.throwSubstitutionError return . normalizeSubstitution

    normalize1
        ::  forall variable
        .   SubstitutionVariable variable
        =>  ( Syntax.Predicate variable
            , Map (UnifiedVariable variable) (TermLike variable)
            )
        ->  unifier (Predicate variable)
    normalize1 (predicate, deduplicated) = do
        normalized <- normalizeSubstitution' deduplicated
        return $ Predicate.fromPredicate predicate <> normalized

original
    :: forall simplifier
    .  MonadSimplify simplifier
    => SubstitutionSimplifier simplifier
original =
    SubstitutionSimplifier worker
  where
    worker substitution = maybeUnwrapSubstitution substitution $ do
        -- We collect all the results here because we should promote the
        -- substitution to the predicate when there is an error on *any* branch.
        results <-
            Unifier.normalizeOnce (Predicate.fromSubstitution substitution)
            & Unifier.maybeUnifierT
        return (OrPredicate.fromPredicates results)

maybeUnwrapSubstitution
    :: (SubstitutionVariable variable, Monad monad)
    => Substitution variable
    -> MaybeT monad (OrPredicate variable)
    -> monad (OrPredicate variable)
maybeUnwrapSubstitution substitution =
    let unwrapped =
            OrPredicate.fromPredicate
            . Predicate.fromPredicate
            . Syntax.Predicate.markSimplified
            -- TODO (thomas.tuegel): Promoting the entire substitution
            -- to the predicate is a problem. We should only promote the
            -- part which has cyclic dependencies.
            $ Syntax.Predicate.fromSubstitution substitution
    in maybeT (return unwrapped) return
