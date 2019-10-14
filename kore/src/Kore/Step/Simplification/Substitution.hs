{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

 -}

module Kore.Step.Simplification.Substitution
    ( SubstitutionSimplifier (..)
    , simplification
    , unification
    , fromNormalization
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
import qualified Data.Map.Strict as Map

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
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.SubstitutionNormalization
    ( Normalization (..)
    , normalize
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
    worker substitution = maybeUnwrapSubstitution $ do
        deduplicated <-
            -- TODO (thomas.tuegel): If substitution de-duplication fails with a
            -- unification error, this will still discard the entire
            -- substitution into the predicate. Fortunately, that seems to be
            -- rare enough to discount for now.
            Unifier.deduplicateSubstitution substitution
            & Unifier.maybeUnifierT
        OrPredicate.fromPredicates <$> traverse normalize1 deduplicated
      where
        maybeUnwrapSubstitution =
            let unwrapped =
                    OrPredicate.fromPredicate
                    . Predicate.fromPredicate
                    . Syntax.Predicate.markSimplified
                    -- TODO (thomas.tuegel): Promoting the entire substitution
                    -- to the predicate is a problem. We should only promote the
                    -- part which has cyclic dependencies.
                    $ Syntax.Predicate.fromSubstitution substitution
            in maybeT (return unwrapped) return

    normalize1 Predicate.Conditional { predicate, substitution } = do
        let deduplicated = Map.fromList $ Substitution.unwrap substitution
            normalized =
                maybe Predicate.bottom fromNormalization
                $ normalize deduplicated
        return $ Predicate.fromPredicate predicate <> normalized

fromNormalization
    :: SubstitutionVariable variable
    => Normalization variable
    -> Predicate variable
fromNormalization Normalization { normalized, denormalized } =
    predicate' <> substitution'
  where
    predicate' =
        Predicate.fromPredicate
        . Syntax.Predicate.fromSubstitution
        $ Substitution.wrap denormalized
    substitution' =
        Predicate.fromSubstitution
        $ Substitution.unsafeWrap normalized

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
        :: forall variable
        .  SubstitutionVariable variable
        => Predicate variable
        -> unifier (Predicate variable)
    normalize1 Predicate.Conditional { predicate, substitution } = do
        let deduplicated = Map.fromList $ Substitution.unwrap substitution
        normalized <- normalizeSubstitution' deduplicated
        return $ Predicate.fromPredicate predicate <> normalized
