{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

{-# OPTIONS_GHC -fno-prof-auto #-}

module Kore.Unification.UnifierT
    ( UnifierT (..)
    , lowerExceptT
    , runUnifierT
    , maybeUnifierT
    , evalEnvUnifierT
    , substitutionSimplifier
    -- * Re-exports
    , module Kore.Unification.Unify
    ) where

import Prelude.Kore

import Control.Error
import Control.Monad
    ( MonadPlus
    )
import qualified Control.Monad.Except as Error
import qualified Control.Monad.Morph as Morph
import Control.Monad.Reader
    ( MonadReader (..)
    )
import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )
import Control.Monad.Trans.Reader
    ( ReaderT (..)
    , mapReaderT
    )

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step.Simplification.CeilSimplifier
    ( CeilSimplifier (..)
    )
import qualified Kore.Step.Simplification.Condition as ConditionSimplifier
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Simplify
    ( ConditionSimplifier (..)
    , InternalVariable
    , MonadSimplify (..)
    )
import Kore.Unification.Error
import Kore.Unification.SubstitutionSimplifier
    ( substitutionSimplifier
    )
import Kore.Unification.Unify
import Log
    ( MonadLog (..)
    )
import SMT
    ( MonadSMT (..)
    )

newtype UnifierT (m :: * -> *) a =
    UnifierT
        { getUnifierT
            :: ReaderT
                (ConditionSimplifier (UnifierT m))
                (BranchT (ExceptT UnificationError m))
                a
        }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift . lift
    {-# INLINE lift #-}

deriving instance MonadReader (ConditionSimplifier (UnifierT m)) (UnifierT m)

deriving instance MonadLog m => MonadLog (UnifierT m)

deriving instance MonadSMT m => MonadSMT (UnifierT m)

deriving instance MonadProfiler m => MonadProfiler (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localSimplifierTermLike locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                (BranchT.mapBranchT
                    (Morph.hoist (localSimplifierTermLike locally))
                )
                readerT
    {-# INLINE localSimplifierTermLike #-}

    localSimplifierAxioms locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                (BranchT.mapBranchT
                    (Morph.hoist (localSimplifierAxioms locally))
                )
                readerT
    {-# INLINE localSimplifierAxioms #-}

    simplifyCondition sideCondition condition = do
        ConditionSimplifier conditionSimplifier <- ask
        conditionSimplifier sideCondition condition
    {-# INLINE simplifyCondition #-}

instance MonadSimplify m => MonadUnify (UnifierT m) where
    throwUnificationError = UnifierT . lift . lift . Error.throwError
    {-# INLINE throwUnificationError #-}

    gather (UnifierT readerT) =
        UnifierT $ mapReaderT (lift . BranchT.gather) readerT
    {-# INLINE gather #-}

    scatter ta =
        UnifierT . ReaderT $ const (BranchT.scatter ta)
    {-# INLINE scatter #-}

-- | Lower an 'ExceptT UnificationError' into a 'MonadUnify'.
lowerExceptT
    :: MonadUnify unifier
    => ExceptT UnificationError unifier a
    -> unifier a
lowerExceptT e = runExceptT e >>= either throwUnificationError pure

runUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> ( forall variable
        . CeilSimplifier (UnifierT m) (TermLike variable) (OrCondition variable)
       )
    -> UnifierT m a
    -> m (Either UnificationError [a])
runUnifierT notSimplifier ceilSimplifier =
    runExceptT
    . BranchT.gather
    . evalEnvUnifierT notSimplifier ceilSimplifier

{- | Run a 'Unifier', returning 'Nothing' upon error.
 -}
maybeUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> ( forall variable
        . CeilSimplifier (UnifierT m) (TermLike variable) (OrCondition variable)
       )
    -> UnifierT m a
    -> MaybeT m [a]
maybeUnifierT notSimplifier ceilSimplifier =
    hushT
    . BranchT.gather
    . evalEnvUnifierT notSimplifier ceilSimplifier

evalEnvUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> ( forall variable
        . CeilSimplifier (UnifierT m) (TermLike variable) (OrCondition variable)
       )
    -> UnifierT m a
    -> BranchT (ExceptT UnificationError m) a
evalEnvUnifierT notSimplifier ceilSimplifier =
    flip runReaderT conditionSimplifier
    . getUnifierT
  where
    conditionSimplifier =
        ConditionSimplifier.create (substitutionSimplifier notSimplifier ceilSimplifier)
