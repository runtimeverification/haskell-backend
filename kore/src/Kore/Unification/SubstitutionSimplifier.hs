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

import qualified Control.Lens as Lens
import Control.Monad
    ( unless
    )
import qualified Control.Monad.State.Class as State
import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.Trans as Trans
import Control.Monad.Trans.Accum
    ( AccumT
    )
import qualified Control.Monad.Trans.Accum as Accum
import Data.Function
    ( (&)
    )
import Data.Generics.Product.Fields
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map

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
        loop substitution
        & flip Accum.execAccumT mempty
        & flip evalStateT maxBound
        & fmap OrCondition.fromCondition

    loop
        ::  forall variable
        .   SubstitutionVariable variable
        =>  Substitution variable
        ->  AccumT (Condition variable) (StateT DenormalizedCount unifier) ()
    loop substitution = do
        deduplicated <- deduplicate substitution
        case Substitution.normalize deduplicated of
            Nothing -> do
                Accum.add Condition.bottom
                return ()
            Just normalization@Normalization { denormalized }
              | null denormalized -> do
                Accum.add $ Condition.fromNormalizationSimplified normalization
                return ()
              | otherwise ->
                simplifyNormalization normalization
                >>= loop . Substitution.wrapNormalization

    updateCount
        :: SimplifierVariable variable
        => UnwrappedSubstitution variable
        -> StateT DenormalizedCount unifier ()
    updateCount denorm = do
        lastCount <- State.get
        let thisCount = length variables
        unless (thisCount < lastCount) (simplifiableCycle variables)
        State.put thisCount
      where
        (variables, _) = unzip denorm

    simplifyNormalization
        ::  forall variable
        .   SubstitutionVariable variable
        =>  Normalization variable
        ->  AccumT (Condition variable) (StateT DenormalizedCount unifier) (Normalization variable)
    simplifyNormalization normalization = do
        let Normalization { denormalized } = normalization
        Trans.lift $ updateCount denormalized
        return normalization
            >>= simplifyNormalized
            >>= return . applyNormalized
            >>= simplifyDenormalized

    simplifyNormalized
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => Normalization variable
        -> AccumT (Condition variable) simplifier (Normalization variable)
    simplifyNormalized =
        Lens.traverseOf (field @"normalized" . Lens.traversed) simplify

    simplifyDenormalized
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => Normalization variable
        -> AccumT (Condition variable) simplifier (Normalization variable)
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
        -> AccumT (Condition variable) simplifier (SingleSubstitution variable)
    simplify subst@(uVar, _) =
        case uVar of
            SetVar _ -> return subst
            ElemVar _ -> traverse simplify1 subst

    simplify1
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => TermLike variable
        -> AccumT (Condition variable) simplifier (TermLike variable)
    simplify1 termLike = do
        orPattern <- Simplifier.simplifyTerm termLike
        case OrPattern.toPatterns orPattern of
            [        ] -> do
                Accum.add Condition.bottom
                return termLike
            [pattern1] -> do
                let (termLike1, condition) = Pattern.splitTerm pattern1
                Accum.add condition
                return termLike1
            _          -> return termLike

    deduplicate
        :: SimplifierVariable variable
        => Substitution variable
        -> AccumT (Condition variable) (StateT DenormalizedCount unifier)
            (Map (UnifiedVariable variable) (TermLike variable))
    deduplicate substitution = do
        (predicate, substitution') <-
            deduplicateSubstitution unificationMakeAnd substitution
            & Trans.lift . Trans.lift
        Accum.add $ Condition.fromPredicate predicate
        return substitution'

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
