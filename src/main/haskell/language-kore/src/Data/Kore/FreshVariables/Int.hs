{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.FreshVariables.Int ( FreshVariablesClass(..)
                                    , FreshVariables
                                    , FreshVariablesT
                                    , IntVariable(..)
                                    , runFreshVariables
                                    , runFreshVariablesT
                                    , MonadTrans (lift)
                                    ) where

import           Control.Monad.Identity         (Identity, runIdentity)
import           Control.Monad.State            (MonadState (get, put),
                                                 MonadTrans (lift), StateT (..),
                                                 modify)

import           Data.Kore.AST
import           Data.Kore.FreshVariables.Class

class VariableClass var => IntVariable var where
    intVariable :: IsMeta a => var a -> Int -> var a

newtype FreshVariablesT m a = FreshVariablesT { inner :: StateT Int m a }

runFreshVariablesT :: FreshVariablesT m a -> Int -> m (a, Int)
runFreshVariablesT = runStateT . inner

type FreshVariables = FreshVariablesT Identity

runFreshVariables :: FreshVariables a -> Int -> (a, Int)
runFreshVariables fva = runIdentity . runFreshVariablesT fva

instance Monad m => Functor (FreshVariablesT m) where
    fmap f = FreshVariablesT . fmap f . inner

instance Monad m => Applicative (FreshVariablesT m) where
    pure = FreshVariablesT . pure
    af <*> aa = FreshVariablesT (inner af <*> inner aa)

instance Monad m => Monad (FreshVariablesT m) where
    return = pure
    ma >>= k = FreshVariablesT (inner ma >>= \ a -> inner (k a))

instance Monad m => MonadState Int (FreshVariablesT m) where
    get = FreshVariablesT get
    put = FreshVariablesT . put

instance MonadTrans FreshVariablesT where
    lift = FreshVariablesT . lift

instance (Monad m, IntVariable var)
    => FreshVariablesClass (FreshVariablesT m) var where
    freshVariable var = do
        counter <- get
        modify (+1)
        return (intVariable var counter)

instance IntVariable Variable where
    intVariable var n = var
        { variableName = Id ((if isMeta var then "#var" else "var") ++ show n)
        }


