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

import Control.Monad
    ( unless
    )
import qualified Control.Monad.State.Class as State
import Control.Monad.State.Strict
    ( StateT
    , evalStateT
    )
import qualified Control.Monad.Trans as Trans
import Data.Function
    ( (&)
    )
import qualified Data.Map.Strict as Map

import qualified Branch as BranchT
import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
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
        => [UnifiedVariable variable]
        -> StateT DenormalizedCount unifier ()
    updateCount variables = do
        lastCount <- State.get
        let thisCount = length variables
        unless (thisCount < lastCount) (simplifiableCycle variables)
        State.put thisCount

    simplifyNormalization
        ::  forall variable
        .   SubstitutionVariable variable
        =>  Condition variable
        ->  Normalization variable
        ->  StateT DenormalizedCount unifier (Condition variable)
    simplifyNormalization condition0 normalization = do
        updateCount variables
        simplified1 <- collectConditions <$> Trans.lift (traverse simplify normalized)
        let (normalized', condition1) = Conditional.splitTerm simplified1
            substitution = Map.fromList normalized'
            denormalized' = (fmap . fmap) (TermLike.substitute substitution) denormalized
        simplified2 <- collectConditions <$> Trans.lift (traverse simplify denormalized')
        let (denormalized'', condition2) = Conditional.splitTerm simplified2
            substitution1 = Condition.fromSubstitution (Substitution.wrap normalized')
            substitution2 = Condition.fromSubstitution (Substitution.wrap denormalized'')
        (return . mconcat)
            [ condition0
            , condition1
            , condition2
            , substitution1
            , substitution2
            ]
      where
        Normalization { normalized, denormalized } = normalization
        (variables, _) = unzip denormalized

    collectConditions
        :: (Traversable t, SubstitutionVariable variable)
        => t (Conditional variable a)
        -> Conditional variable (t a)
    collectConditions = sequenceA

    simplify
        :: SimplifierVariable variable
        => (UnifiedVariable variable, TermLike variable)
        -> unifier (Conditional variable (UnifiedVariable variable, TermLike variable))
    simplify subst@(uVar, _) =
        case uVar of
            SetVar _ -> return (pure subst)
            ElemVar _ -> collectConditions <$> traverse simplify1 subst

    simplify1
        :: SimplifierVariable variable
        => TermLike variable
        -> unifier (Pattern variable)
    simplify1 termLike = do
        orPattern <- Simplifier.simplifyTerm termLike
        case OrPattern.toPatterns orPattern of
            [        ] -> return $ Pattern.bottomOf (TermLike.termLikeSort termLike)
            [pattern1] -> return pattern1
            _          -> return $ Pattern.fromTermLike termLike

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
