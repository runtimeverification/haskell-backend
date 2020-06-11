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

import Kore.Profiler.Data
    ( MonadProfiler
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
                (LogicT (ExceptT UnificationError m))
                a
        }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift . lift
    {-# INLINE lift #-}

deriving instance MonadLog m => MonadLog (UnifierT m)

deriving instance Monad m => MonadLogic (UnifierT m)

deriving instance MonadProfiler m => MonadProfiler (UnifierT m)

deriving instance MonadReader (ConditionSimplifier (UnifierT m)) (UnifierT m)

deriving instance MonadSMT m => MonadSMT (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localSimplifierTermLike locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                (mapLogicT
                    (Morph.hoist (localSimplifierTermLike locally))
                )
                readerT
    {-# INLINE localSimplifierTermLike #-}

    localSimplifierAxioms locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                (mapLogicT
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

-- | Lower an 'ExceptT UnificationError' into a 'MonadUnify'.
lowerExceptT
    :: MonadUnify unifier
    => ExceptT UnificationError unifier a
    -> unifier a
lowerExceptT e = runExceptT e >>= either throwUnificationError pure

runUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> UnifierT m a
    -> m (Either UnificationError [a])
runUnifierT notSimplifier =
    runExceptT
    . observeAllT
    . evalEnvUnifierT notSimplifier

{- | Run a 'Unifier', returning 'Nothing' upon error.
 -}
maybeUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> UnifierT m a
    -> MaybeT m [a]
maybeUnifierT notSimplifier =
    hushT
    . observeAllT
    . evalEnvUnifierT notSimplifier

evalEnvUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> UnifierT m a
    -> LogicT (ExceptT UnificationError m) a
evalEnvUnifierT notSimplifier =
    flip runReaderT conditionSimplifier
    . getUnifierT
  where
    conditionSimplifier =
        ConditionSimplifier.create (substitutionSimplifier notSimplifier)
