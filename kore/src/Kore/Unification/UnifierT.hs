{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Unification.UnifierT (
    UnifierT (..),
    runUnifierT,
    evalEnvUnifierT,
    substitutionSimplifier,

    -- * Re-exports
    module Kore.Unification.Unify,
) where

import Control.Monad.Reader (
    MonadReader (..),
 )
import Control.Monad.Trans.Reader (
    ReaderT (..),
    mapReaderT,
 )
import Data.Kind (
    Type,
 )
import Kore.Simplify.Condition qualified as ConditionSimplifier
import Kore.Simplify.NotSimplifier
import Kore.Simplify.Simplify (
    ConditionSimplifier (..),
    MonadSimplify (..),
    Simplifier,
 )
import Kore.Unification.SubstitutionSimplifier (
    substitutionSimplifier,
 )
import Kore.Unification.Unify
import Log (
    MonadLog (..),
 )
import Prelude.Kore
import SMT (
    MonadSMT (..),
 )

newtype UnifierT (m :: Type -> Type) a = UnifierT
    { getUnifierT ::
        ReaderT
            (ConditionSimplifier (UnifierT m))
            (LogicT m)
            a
    }
    deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)
    deriving newtype (MonadIO)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift
    {-# INLINE lift #-}

deriving newtype instance MonadLog m => MonadLog (UnifierT m)

deriving newtype instance Monad m => MonadLogic (UnifierT m)

deriving newtype instance
    MonadReader (ConditionSimplifier (UnifierT m)) (UnifierT m)

deriving newtype instance MonadSMT m => MonadSMT (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localAxiomEquations locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                ( mapLogicT
                    (localAxiomEquations locally)
                )
                readerT
    {-# INLINE localAxiomEquations #-}

    simplifyCondition sideCondition condition = do
        ConditionSimplifier conditionSimplifier <- ask
        conditionSimplifier sideCondition condition
    {-# INLINE simplifyCondition #-}

instance MonadSimplify m => MonadUnify (UnifierT m)

runUnifierT ::
    NotSimplifier Simplifier =>
    UnifierT Simplifier a ->
    Simplifier [a]
runUnifierT = observeAllT . evalEnvUnifierT

evalEnvUnifierT ::
    NotSimplifier Simplifier =>
    UnifierT Simplifier a ->
    LogicT Simplifier a
evalEnvUnifierT =
    flip runReaderT conditionSimplifier
        . getUnifierT
  where
    conditionSimplifier =
        ConditionSimplifier.create substitutionSimplifier
