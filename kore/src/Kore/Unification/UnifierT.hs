{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

{-# OPTIONS_GHC -fno-prof-auto #-}

module Kore.Unification.UnifierT
    ( UnifierT (..)
    , runUnifierT
    , evalEnvUnifierT
    , substitutionSimplifier
    -- * Re-exports
    , module Kore.Unification.Unify
    ) where

import Prelude.Kore

import Control.Monad
    ( MonadPlus
    )
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

import qualified Kore.Step.Simplification.Condition as ConditionSimplifier
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Simplify
    ( ConditionSimplifier (..)
    , InternalVariable
    , MonadSimplify (..)
    )
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
                (LogicT m)
                a
        }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift
    {-# INLINE lift #-}

deriving instance MonadLog m => MonadLog (UnifierT m)

deriving instance Monad m => MonadLogic (UnifierT m)

deriving instance MonadReader (ConditionSimplifier (UnifierT m)) (UnifierT m)

deriving instance MonadSMT m => MonadSMT (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localSimplifierAxioms locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                (mapLogicT
                    (localSimplifierAxioms locally)
                )
                readerT
    {-# INLINE localSimplifierAxioms #-}

    simplifyCondition sideCondition condition = do
        ConditionSimplifier conditionSimplifier <- ask
        conditionSimplifier sideCondition condition
    {-# INLINE simplifyCondition #-}

instance MonadSimplify m => MonadUnify (UnifierT m) where

runUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> UnifierT m a
    -> m [a]
runUnifierT notSimplifier =
    observeAllT
    . evalEnvUnifierT notSimplifier

evalEnvUnifierT
    :: MonadSimplify m
    => NotSimplifier (UnifierT m)
    -> UnifierT m a
    -> LogicT m a
evalEnvUnifierT notSimplifier =
    flip runReaderT conditionSimplifier
    . getUnifierT
  where
    conditionSimplifier =
        ConditionSimplifier.create (substitutionSimplifier notSimplifier)
