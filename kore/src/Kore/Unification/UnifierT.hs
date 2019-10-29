{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Unification.UnifierT
    ( UnifierT (..)
    , throwUnificationOrSubstitutionError
    , lowerExceptT
    , runUnifierT
    , maybeUnifierT
    , substitutionSimplifier
    , unificationMakeAnd
    -- * Re-exports
    , module Kore.Unification.Unify
    ) where

import Control.Applicative
    ( Alternative
    )
import Control.Error
import Control.Monad
    ( MonadPlus
    )
import qualified Control.Monad.Except as Error
import qualified Control.Monad.Morph as Morph
import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )
import Data.Map.Strict
    ( Map
    )

import Branch
    ( BranchT
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
import Kore.Logger
    ( MonadLog (..)
    )
import Kore.Predicate.Predicate
    ( Predicate
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Condition as ConditionSimplifier
import Kore.Step.Simplification.Simplify
    ( ConditionSimplifier (..)
    , MonadSimplify (..)
    , SimplifierVariable
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
    ( Substitution
    )
import Kore.Unification.SubstitutionNormalization
    ( normalizeSubstitution
    )
import Kore.Unification.Unify
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )
import SMT
    ( MonadSMT (..)
    )

newtype UnifierT (m :: * -> *) a =
    UnifierT
        { getUnifierT :: BranchT (ExceptT UnificationOrSubstitutionError m) a }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift
    {-# INLINE lift #-}

deriving instance MonadLog m => MonadLog (UnifierT m)

deriving instance MonadSMT m => MonadSMT (UnifierT m)

deriving instance MonadProfiler m => MonadProfiler (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localSimplifierTermLike locally =
        \(UnifierT branchT) ->
            UnifierT
                (BranchT.mapBranchT
                    (Morph.hoist (localSimplifierTermLike locally))
                    branchT
                )
    {-# INLINE localSimplifierTermLike #-}

    localSimplifierAxioms locally =
        \(UnifierT branchT) ->
            UnifierT
                (BranchT.mapBranchT
                    (Morph.hoist (localSimplifierAxioms locally))
                    branchT
                )
    {-# INLINE localSimplifierAxioms #-}

    simplifyCondition = simplifyCondition'
      where
        ConditionSimplifier simplifyCondition' =
            ConditionSimplifier.create substitutionSimplifier
    {-# INLINE simplifyCondition #-}

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
        fmap OrCondition.fromConditions . gather $ do
            deduplicated <-
                deduplicateSubstitution
                    unificationMakeAnd
                    substitution
            normalize1 deduplicated

    normalizeSubstitution'
        :: forall variable
        .  SubstitutionVariable variable
        => Map (UnifiedVariable variable) (TermLike variable)
        -> unifier (Condition variable)
    normalizeSubstitution' =
        either throwSubstitutionError return . normalizeSubstitution

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

instance MonadSimplify m => MonadUnify (UnifierT m) where
    throwSubstitutionError =
        UnifierT
        . lift
        . Error.throwError
        . SubstitutionError
    {-# INLINE throwSubstitutionError #-}

    throwUnificationError =
        UnifierT
        . lift
        . Error.throwError
        . UnificationError
    {-# INLINE throwUnificationError #-}

    gather = UnifierT . lift . BranchT.gather . getUnifierT
    {-# INLINE gather #-}

    scatter = UnifierT . BranchT.scatter
    {-# INLINE scatter #-}

-- | Lower an 'ExceptT UnificationOrSubstitutionError' into a 'MonadUnify'.
lowerExceptT
    :: MonadUnify unifier
    => ExceptT UnificationOrSubstitutionError unifier a
    -> unifier a
lowerExceptT e =
    runExceptT e >>= either throwUnificationOrSubstitutionError pure

throwUnificationOrSubstitutionError
    :: MonadUnify unifier
    => UnificationOrSubstitutionError
    -> unifier a
throwUnificationOrSubstitutionError (SubstitutionError s) =
    throwSubstitutionError s
throwUnificationOrSubstitutionError (UnificationError u) =
    throwUnificationError u

runUnifierT
    :: MonadSimplify m
    => UnifierT m a
    -> m (Either UnificationOrSubstitutionError [a])
runUnifierT = runExceptT . BranchT.gather . getUnifierT

{- | Run a 'Unifier', returning 'Nothing' upon error.
 -}
maybeUnifierT :: MonadSimplify m => UnifierT m a -> MaybeT m [a]
maybeUnifierT = hushT . BranchT.gather . getUnifierT

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        unified <- termUnification termLike1 termLike2
        BranchT.alternate
            $ Simplifier.simplifyCondition
            $ Pattern.andCondition unified condition
