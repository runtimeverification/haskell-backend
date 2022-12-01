{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
{-# LANGUAGE CPP #-}
module Logic (
    module Control.Monad.Logic,
    module Control.Monad.Trans,
    module Control.Monad,
    gather,
    scatter,
    mapLogicT,
    lowerLogicT,
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Trans
import Prelude

gather :: MonadLogic m => m a -> m [a]
gather acts =
    msplit acts >>= \case
        Nothing -> return []
        Just (a, acts') -> (:) a <$> gather acts'
{-# INLINE gather #-}

scatter :: (Foldable f, Alternative m) => f a -> m a
scatter = foldr ((<|>) . pure) empty
{-# INLINE scatter #-}

mapLogicT ::
    (Monad m, Monad n) =>
    (forall x. m x -> n x) ->
    LogicT m a ->
    LogicT n a
mapLogicT nat acts = hoistLogicT nat acts
{-# INLINE mapLogicT #-}
#if !MIN_VERSION_logict(0,8,0)
-- Copied from logict
fromLogicTWith :: (Applicative m, Monad n, Alternative n)
  => (forall x. m x -> n x) -> LogicT m a -> n a
fromLogicTWith p (LogicT f) = join . p $
  f (\a v -> pure (pure a <|> join (p v))) (pure empty)

hoistLogicT :: (Applicative m, Monad n) => (forall x. m x -> n x) -> LogicT m a -> LogicT n a
hoistLogicT f = fromLogicTWith (lift . f)
#endif

lowerLogicT :: Alternative m => LogicT m a -> m a
lowerLogicT acts = unLogicT acts (\a mr -> pure a <|> mr) empty
{-# INLINE lowerLogicT #-}
