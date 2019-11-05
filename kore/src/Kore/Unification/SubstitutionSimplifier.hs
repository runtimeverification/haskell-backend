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
import qualified Data.Map.Strict as Map

import qualified Branch as BranchT
import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
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
        flip evalStateT maxBound
        $ OrCondition.fromCondition <$> loop (Condition.fromSubstitution substitution)

    loop
        ::  forall variable
        .   SubstitutionVariable variable
        =>  Condition variable
        ->  StateT DenormalizedCount unifier (Condition variable)
    loop Conditional { term = (), predicate, substitution } = do
        (predicate', deduplicated) <- deduplicate substitution
        let predicates = fromPredicates [predicate, predicate']
        case Substitution.normalize deduplicated of
            Nothing -> return Condition.bottom
            Just normalization@Normalization { denormalized }
              | null denormalized -> return $ predicates <> condition
              | otherwise -> simplifyNormalization predicates normalization >>= loop
              where
                condition = Condition.fromNormalizationSimplified normalization

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
        =>  Condition variable
        ->  Normalization variable
        ->  StateT DenormalizedCount unifier (Condition variable)
    simplifyNormalization condition normalization = do
        let Normalization { denormalized } = normalization
        updateCount denormalized
        return normalization
            >>= simplifyNormalized
            >>= return . applyNormalized
            >>= simplifyDenormalized
            >>= addNormalization
            & flip Accum.execAccumT condition

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

    addNormalization
        :: (Monad monad, SimplifierVariable variable)
        => Normalization variable
        -> AccumT (Condition variable) monad ()
    addNormalization =
        Accum.add . Condition.fromSubstitution . Substitution.wrapNormalization

    simplify
        :: (MonadSimplify simplifier, SimplifierVariable variable)
        => (UnifiedVariable variable, TermLike variable)
        -> AccumT (Condition variable) simplifier (UnifiedVariable variable, TermLike variable)
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

    deduplicate substitution =
        deduplicateSubstitution unificationMakeAnd substitution & Trans.lift

    fromPredicates predicates = mconcat (map Condition.fromPredicate predicates)

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
