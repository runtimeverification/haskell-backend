{-# LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Accum.Stricter
-- Copyright   :  (c) Nickolay Kudasov 2016
-- License     :  BSD-style (see the file LICENSE)
--
-- Stability   :  experimental
-- Portability :  portable
--
-- A very strict version of @AccumT@, which accumulates its
-- state strictly.
-----------------------------------------------------------------------------

module Control.Monad.Trans.Accum.Stricter (
    -- * The Accum monad
    Accum,
    accum,
    runAccum,
    execAccum,
    evalAccum,
    mapAccum,
    -- * The AccumT monad transformer
    AccumT(AccumT),
    runAccumT,
    execAccumT,
    evalAccumT,
    mapAccumT,
    -- * Accum operations
    look,
    looks,
    add,
  ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Functor.Identity

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.Fix
import GHC.Generics (Generic)

-- ---------------------------------------------------------------------------
-- | An accumulation monad parameterized by the type @w@ of output to accumulate.
--
-- The 'return' function produces the output 'mempty', while @>>=@
-- combines the outputs of the subcomputations using 'mappend'.
type Accum w = AccumT w Identity

-- | Construct an accumulation computation from a (result, output) pair.
-- (The inverse of 'runAccum'.)
accum :: (Monad m) => (w -> (a, w)) -> AccumT w m a
accum f = AccumT $ \ !w -> pure (f w)
{-# INLINE accum #-}

-- | Unwrap an accumulation computation as a (result, output) pair.
-- (The inverse of 'accum'.)
runAccum :: Accum w a -> w -> (a, w)
runAccum m = runIdentity . runAccumT m
{-# INLINE runAccum #-}

-- | Extract the output from an accumulation computation.
--
-- * @'execAccum' m w = 'snd' ('runAccum' m w)@
execAccum :: Accum w a -> w -> w
execAccum m w = snd (runAccum m w)
{-# INLINE execAccum #-}

-- | Evaluate an accumulation computation with the given initial output history
-- and return the final value, discarding the final output.
--
-- * @'evalAccum' m w = 'fst' ('runAccum' m w)@
evalAccum :: Accum w a -> w -> a
evalAccum m w = fst (runAccum m w)
{-# INLINE evalAccum #-}

-- | Map both the return value and output of a computation using
-- the given function.
--
-- * @'runAccum' ('mapAccum' f m) = f . 'runAccum' m@
mapAccum :: ((a, w) -> (b, w)) -> Accum w a -> Accum w b
mapAccum f = mapAccumT (Identity . f . runIdentity)
{-# INLINE mapAccum #-}

-- ---------------------------------------------------------------------------
-- | An accumulation monad parameterized by:
--
--   * @w@ - the output to accumulate.
--
--   * @m@ - The inner monad.
--
-- The 'return' function produces the output 'mempty', while @>>=@
-- combines the outputs of the subcomputations using 'mappend'.
--
-- This monad transformer is similar to both state and writer monad transformers.
-- Thus it can be seen as
--
--  * a restricted append-only version of a state monad transformer or
--
--  * a writer monad transformer with the extra ability to read all previous output.
newtype AccumT w m a = AccumT (w -> m (a, w))
    deriving stock Generic

-- | Unwrap an accumulation computation.
runAccumT :: AccumT w m a -> w -> m (a, w)
runAccumT (AccumT f) = f
{-# INLINE runAccumT #-}

-- | Extract the output from an accumulation computation.
--
-- * @'execAccumT' m w = 'liftM' 'snd' ('runAccumT' m w)@
execAccumT :: (Monad m) => AccumT w m a -> w -> m w
execAccumT m w = do
    (_, !w') <- runAccumT m w
    pure w'
{-# INLINE execAccumT #-}

-- | Evaluate an accumulation computation with the given initial output history
-- and return the final value, discarding the final output.
--
-- * @'evalAccumT' m w = 'liftM' 'fst' ('runAccumT' m w)@
evalAccumT :: Monad m => AccumT w m a -> w -> m a
evalAccumT m w = do
    (a, _) <- runAccumT m w
    pure a
{-# INLINE evalAccumT #-}

-- | Map both the return value and output of a computation using
-- the given function.
--
-- * @'runAccumT' ('mapAccumT' f m) = f . 'runAccumT' m@
--
-- This function does not itself force either initial or result
-- accumulators!
mapAccumT :: (m (a, w) -> n (b, w)) -> AccumT w m a -> AccumT w n b
mapAccumT f m = AccumT (f . runAccumT m)
{-# INLINE mapAccumT #-}

instance Monad m => Functor (AccumT w m) where
    fmap f = mapAccumT  (>>= \ (a, !w) -> pure (f a, w))
    {-# INLINE fmap #-}

instance (Monoid w, Functor m, Monad m) => Applicative (AccumT w m) where
    pure a  = AccumT $ \ !_ -> pure (a, mempty)
    {-# INLINE pure #-}
    mf <*> mv = AccumT $ \ w -> do
      (f, !w')  <- runAccumT mf w
      (v, !w'') <- runAccumT mv $! w `mappend` w'
      pure (f v, w' `mappend` w'')
    {-# INLINE (<*>) #-}

instance (Monoid w, Functor m, MonadPlus m) => Alternative (AccumT w m) where
    empty   = AccumT $ \ !_ -> mzero
    {-# INLINE empty #-}
    m <|> n = AccumT $ \ w -> runAccumT m w `mplus` runAccumT n w
    {-# INLINE (<|>) #-}

instance (Monoid w, Functor m, Monad m) => Monad (AccumT w m) where
    m >>= k  = AccumT $ \ !w -> do
        (a, !w')  <- runAccumT m w
        (b, !w'') <- runAccumT (k a) (w `mappend` w')
        pure (b, w' `mappend` w'')
    {-# INLINE (>>=) #-}

instance (Monoid w, Fail.MonadFail m) => Fail.MonadFail (AccumT w m) where
    fail msg = AccumT $ \ !_ -> Fail.fail msg
    {-# INLINE fail #-}

instance (Monoid w, Functor m, MonadPlus m) => MonadPlus (AccumT w m) where
    mzero       = AccumT $ \ !_ -> mzero
    {-# INLINE mzero #-}
    m `mplus` n = AccumT $ \ !w -> runAccumT m w `mplus` runAccumT n w
    {-# INLINE mplus #-}

instance (Monoid w, Functor m, MonadFix m) => MonadFix (AccumT w m) where
    mfix m = AccumT $ \ !w -> mfix $ \ ~(a, _) -> runAccumT (m a) w
    {-# INLINE mfix #-}

instance (Monoid w) => MonadTrans (AccumT w) where
    lift m = AccumT $ \ !_ -> do
        a <- m
        pure (a, mempty)
    {-# INLINE lift #-}

instance (Monoid w, Functor m, MonadIO m) => MonadIO (AccumT w m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}

-- | @'look'@ is an action that fetches all the previously accumulated output.
look :: (Monoid w, Monad m) => AccumT w m w
look = AccumT $ \ !w -> pure (w, mempty)

-- | @'look'@ is an action that retrieves a function of the previously accumulated output.
looks :: (Monoid w, Monad m) => (w -> a) -> AccumT w m a
looks f = AccumT $ \ !w -> pure (f w, mempty)

-- | @'add' w@ is an action that produces the output @w@.
add :: (Monad m) => w -> AccumT w m ()
add !w = accum $ \ !_ -> ((), w)
{-# INLINE add #-}
