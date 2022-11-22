{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Logic (
    module Control.Monad.Logic,
    module Control.Monad.Trans,
    module Control.Monad,
    MonadLogic (..),
    scatter,
    mapLogicT,
    lowerLogicT,
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic hiding (MonadLogic)
import qualified Control.Monad.Logic as LC
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Trans
import Prelude

-- | A version of
-- @"Control.Monad.Logic".'Control.Monad.Logic.MonadLogic'@
-- augmented with an efficient 'gather' method.
class LC.MonadLogic m => MonadLogic m where
    -- Gather all the results of a logic computation within
    -- a logic computation.
    --
    -- @
    -- gather acts =
    --   'msplit' acts >>= \case
    --     Nothing -> pure []
    --     Just (a, acts') -> (a :) <$> gather acts'
    -- @
    gather :: m a -> m [a]

instance Monad m => MonadLogic (LogicT m) where
    gather m = lift (observeAllT m)
    {-# INLINE gather #-}

instance MonadLogic m => MonadLogic (ReaderT e m) where
    gather m = ReaderT $ gather . runReaderT m
    {-# INLINE gather #-}

scatter :: (Foldable f, Alternative m) => f a -> m a
scatter = foldr ((<|>) . pure) empty
{-# INLINE scatter #-}

mapLogicT ::
    (Monad m, Monad n) =>
    (forall x. m x -> n x) ->
    LogicT m a ->
    LogicT n a
mapLogicT nat acts = (lift . nat) (observeAllT acts) >>= scatter
{-# INLINE mapLogicT #-}

lowerLogicT :: Alternative m => LogicT m a -> m a
lowerLogicT acts = unLogicT acts (\a mr -> pure a <|> mr) empty
{-# INLINE lowerLogicT #-}
