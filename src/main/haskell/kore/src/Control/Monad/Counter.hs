{-# LANGUAGE DefaultSignatures #-}

{-|
Module      : Control.Monad.Counter
Description : Monads carrying a monotonically-increasing counter
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

The class 'MonadCounter' describes a monad carrying a monotonically-increasing
counter used for fresh variable generation. The type 'Counter' provides a
concrete implementation of the class.

-}
module Control.Monad.Counter
    ( -- * Class
      MonadCounter (..)
    , findState
    , module Numeric.Natural
      -- * Implementation
    , Counter
    , runCounter, evalCounter
      -- * Transformer
    , CounterT
    , runCounterT, evalCounterT
    ) where

import qualified Control.Monad.Except as Monad.Except
import qualified Control.Monad.Identity as Monad.Identity
import qualified Control.Monad.Reader as Monad.Reader
import qualified Control.Monad.RWS.Lazy as Monad.RWS.Lazy
import qualified Control.Monad.RWS.Strict as Monad.RWS.Strict
import           Control.Monad.State
                 ( MonadState )
import qualified Control.Monad.State.Class as Monad.State
import qualified Control.Monad.State.Lazy as Monad.State.Lazy
import qualified Control.Monad.State.Strict as Monad.State.Strict
import           Control.Monad.Trans
                 ( MonadTrans )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Control.Monad.Writer.Lazy as Monad.Writer.Lazy
import qualified Control.Monad.Writer.Strict as Monad.Writer.Strict
import           Numeric.Natural

-- * Class

{- | @MonadCounter@ abstracts a state monad carrying a monotonic counter.

  The counter is generally used for fresh variable generation. The interface is
  intended to be safer than a 'MonadState' instance, which could accidentally be
  reset. @MonadCounter@ also allows /monotonic/ access to the counter (and
  /only/ the counter) in a monad with more complex state.

  A default implementation is provided for instances of @MonadState Natural@.

 -}
class Monad m => MonadCounter m where
    {- | Increment the counter and return the prior value.

      Using the @MonadCounter@ interface instead of the 'MonadState' instance
      ensures that the counter cannot accidentally be reset, which could
      generate duplicate fresh variables.
     -}
    increment :: m Natural
    default increment :: MonadState Natural m => m Natural
    increment = do
        n <- Monad.State.get
        Monad.State.modify' succ
        return n

instance MonadCounter m => MonadCounter (Monad.Except.ExceptT e m) where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance MonadCounter m => MonadCounter (Monad.Identity.IdentityT m) where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance
    (MonadCounter m, Monoid w) =>
    MonadCounter (Monad.RWS.Lazy.RWST r w s m)
  where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance
    (MonadCounter m, Monoid w) =>
    MonadCounter (Monad.RWS.Strict.RWST r w s m)
  where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance MonadCounter m => MonadCounter (Monad.Reader.ReaderT r m) where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance MonadCounter m => MonadCounter (Monad.State.Lazy.StateT s m) where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance MonadCounter m => MonadCounter (Monad.State.Strict.StateT s m) where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance
    (MonadCounter m, Monoid w) =>
    MonadCounter (Monad.Writer.Lazy.WriterT w m)
  where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

instance
    (MonadCounter m, Monoid w) =>
    MonadCounter (Monad.Writer.Strict.WriterT w m)
  where
    increment = Monad.Trans.lift increment
    {-# INLINE increment #-}

{- | Execute a list of actions until one satisfies the given predicate.

  The state is reset after any action that does not satisfy the predicate.

 -}
findState
    :: MonadState s m
    => (a -> Bool)
    -- ^ predicate
    -> [m a]
    -- ^ actions
    -> m (Maybe a)
findState predicate = findState0
  where
    findState0 [] = return Nothing
    findState0 (action : actions) =
        do
            s <- Monad.State.get
            a <- action
            if predicate a
                then return (Just a)
                else do
                    Monad.State.put s
                    findState0 actions

-- * Implementation

{- | A computation using a monotonic counter.
 -}
newtype Counter a = Counter (Monad.State.Strict.State Natural a)
  deriving (Applicative, Functor, Monad)

-- | The @MonadState@ instance must not be used to replay the counter!
deriving instance MonadState Natural Counter

instance MonadCounter Counter

{- | Run a computation using a monotonic counter.

  The counter is initialized to the given value. The final result and counter
  are returned.

 -}
runCounter
    :: Counter a
    -- ^ computation
    -> Natural
    -- ^ initial counter
    -> (a, Natural)
runCounter (Counter counting) = Monad.State.Strict.runState counting

{- | Return the final result of a computation using a monotonic counter.

  The counter is initialized to @0@.

 -}
evalCounter :: Counter a -> a
evalCounter (Counter counting) =
    let (a, _) = Monad.State.Strict.runState counting 0 in a

-- * Transformer

newtype CounterT m a = CounterT (Monad.State.Strict.StateT Natural m a)
    deriving (Applicative, Functor, Monad)

-- | The @MonadState@ instance must not be used to replay the counter!
deriving instance Monad m => MonadState Natural (CounterT m)

instance Monad m => MonadCounter (CounterT m)

instance MonadTrans CounterT where
    lift m = CounterT (Monad.Trans.lift m)

{- | Run a computation using a monotonic counter.

  The counter is initialized to the given value. The final result and counter
  are returned.

 -}
runCounterT
    :: CounterT m a
    -- ^ computation
    -> Natural
    -- ^ initial counter
    -> m (a, Natural)
runCounterT (CounterT counting) = Monad.State.Strict.runStateT counting

{- | Return the final result of a computation using a monotonic counter.

  The counter is initialized to @0@.

 -}
evalCounterT :: Monad m => CounterT m a -> m a
evalCounterT (CounterT counting) =
    do
        (a, _) <- Monad.State.Strict.runStateT counting 0
        return a
