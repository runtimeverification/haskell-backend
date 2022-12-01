{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Logic (
    module Control.Monad.Logic.Class,
    module Control.Monad.Logic.Sequence,
    module Control.Monad.Trans,
    module Control.Monad,
    gather,
    scatter,
    mapSeqT,
    lowerSeqT,
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic.Class
import Control.Monad.Logic.Sequence
import Control.Monad.Morph
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

-- | The first argument must be a monad morphism to get consistent results. For
-- other functions, 'Control.Monad.Logic.Sequence.Morph.hoistPreUnexposed' may
-- be used instead; the results of that won't depend on the internal structure
-- of the logic computation, but they likely won't behave very intuitively
-- regardless.
mapSeqT ::
    Monad m =>
    (forall x. m x -> n x) ->
    SeqT m a ->
    SeqT n a
mapSeqT nat = hoist nat
{-# INLINE mapSeqT #-}

lowerSeqT :: (Alternative m, Monad m) => SeqT m a -> m a
lowerSeqT (MkSeqT acts) = acts >>= viewT empty (\a ~r -> pure a <|> lowerSeqT r)
{-# INLINE lowerSeqT #-}
