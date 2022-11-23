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
            (SeqT m)
            a
    }
    deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)
    deriving newtype (MonadIO)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift
    {-# INLINE lift #-}

deriving newtype instance MonadLog m => MonadLog (UnifierT m)

instance Monad m => MonadLogic (UnifierT m) where
    msplit (UnifierT m) = UnifierT (fmap (fmap (fmap UnifierT)) (msplit m))

deriving newtype instance
    Monad m => MonadReader (ConditionSimplifier (UnifierT m)) (UnifierT m)

deriving newtype instance MonadSMT m => MonadSMT (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localAxiomEquations locally (UnifierT readerT) =
        UnifierT $
            mapReaderT
                ( mapSeqT
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
    MonadSimplify m =>
    NotSimplifier (UnifierT m) ->
    UnifierT m a ->
    m [a]
runUnifierT notSimplifier =
    observeAllT
        . evalEnvUnifierT notSimplifier

evalEnvUnifierT ::
    MonadSimplify m =>
    NotSimplifier (UnifierT m) ->
    UnifierT m a ->
    SeqT m a
evalEnvUnifierT notSimplifier =
    flip runReaderT conditionSimplifier
        . getUnifierT
  where
    conditionSimplifier =
        ConditionSimplifier.create (substitutionSimplifier notSimplifier)
