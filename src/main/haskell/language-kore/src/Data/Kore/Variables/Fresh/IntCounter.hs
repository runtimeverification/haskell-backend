{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Variables.Fresh.IntCounter ( IntCounter
                                            , IntCounterT
                                            , runIntCounter
                                            , runIntCounterT
                                            ) where

import           Control.Monad.Identity (Identity, runIdentity)
import           Control.Monad.State    (MonadState (get, put),
                                         MonadTrans (lift), StateT (..))

-- |'IntCounterT' is a monad transformer encapsulating an integer counter
newtype IntCounterT m a = IntCounterT { intCounterState :: StateT Int m a }

{-|'runIntCounterT' evaluates the computation with the given initial counter
and yields a value containing the state in the parameter monad.
-}
runIntCounterT :: IntCounterT m a -> Int -> m (a, Int)
runIntCounterT = runStateT . intCounterState

type IntCounter = IntCounterT Identity

runIntCounter :: IntCounter a -> Int -> (a, Int)
runIntCounter fva = runIdentity . runIntCounterT fva

instance Monad m => Functor (IntCounterT m) where
    fmap f = IntCounterT . fmap f . intCounterState

instance Monad m => Applicative (IntCounterT m) where
    pure = IntCounterT . pure
    af <*> aa = IntCounterT (intCounterState af <*> intCounterState aa)

instance Monad m => Monad (IntCounterT m) where
    return = pure
    ma >>= k = IntCounterT (intCounterState ma >>= \ a -> intCounterState (k a))

instance Monad m => MonadState Int (IntCounterT m) where
    get = IntCounterT get
    put = IntCounterT . put

instance MonadTrans IntCounterT where
    lift = IntCounterT . lift
