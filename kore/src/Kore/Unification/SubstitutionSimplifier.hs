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

import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.Trans as Trans
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
import qualified Kore.Internal.Pattern as Pattern
import Kore.Predicate.Predicate
    ( Predicate
    , makeTruePredicate
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
import qualified Kore.Unification.SubstitutionNormalization as Substitution
    ( normalize
    )
import Kore.Unification.Unify

type DenormalizedCount = Int

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
    worker substitution =
        flip evalStateT maxBound
        $ OrCondition.fromCondition <$> loop (makeTruePredicate, substitution)

    deduplicate substitution =
        deduplicateSubstitution unificationMakeAnd substitution & Trans.lift

    fromPredicates predicates = mconcat (map Condition.fromPredicate predicates)

    loop
        ::  forall variable
        .   SubstitutionVariable variable
        =>  (Predicate variable, Substitution variable)
        ->  StateT DenormalizedCount unifier (Condition variable)
    loop (predicate, substitution) = do
        (predicate', deduplicated) <- deduplicate substitution
        let predicates = fromPredicates [predicate, predicate']
        case Substitution.normalize deduplicated of
            Nothing -> return Condition.bottom
            Just normalization@Normalization { denormalized }
              | null denormalized -> return $ predicates <> condition
              | otherwise -> simplifiableCycle variables
              where
                (variables, _) = unzip denormalized
                condition = Condition.fromNormalizationSimplified normalization

    simplifiableCycle variables =
        (Trans.lift . throwSubstitutionError) (SimplifiableCycle variables)

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        unified <- termUnification termLike1 termLike2
        BranchT.alternate
            $ Simplifier.simplifyCondition
            $ Pattern.andCondition unified condition
