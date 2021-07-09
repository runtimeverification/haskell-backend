{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Logic (
    module Control.Monad.Logic,
    gather,
    scatter,
    mapLogicT,
    lowerLogicT,
) where

import Control.Applicative
import Control.Monad.Logic
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
mapLogicT nat acts = (lift . nat) (observeAllT acts) >>= scatter
{-# INLINE mapLogicT #-}

lowerLogicT :: Alternative m => LogicT m a -> m a
lowerLogicT acts = unLogicT acts (\a mr -> pure a <|> mr) empty
{-# INLINE lowerLogicT #-}
