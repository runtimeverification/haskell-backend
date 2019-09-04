{-|
Module      : ListT
Description : List monad transformer
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

This module implements the list monad transformer.

-}

{-# LANGUAGE UndecidableInstances #-}

module ListT
    ( ListT (..)
    , cons
    , gather
    , scatter
    , mapListT
    -- * Re-exports
    , Alternative (..), MonadPlus (..)
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Morph
import Control.Monad.RWS.Class
import Data.Foldable
import Data.Typeable

{- | The list monad transformer written as a right-associative fold.

This representation is similar to the
<https://en.wikipedia.org/wiki/Church_encoding Church encoding> or the
<https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding Scott encoding>.
It inherits the performance benefits of the 'Control.Monad.Codensity.Codensity'
of a free monad.
The first argument of 'foldListT' is a heterogenous analog of 'bind' that
enables streaming instances of 'MFunctor' and 'MMorph'. When @n ~ m@, this
argument is literally 'bind'.

Note that none of its basic instances—e.g. 'Functor', 'Applicative',
'Alternative', 'Monad'—rely on the transformed type @m@ because @ListT@ takes
those behaviors from the instances for lists.

'empty' is related to the empty list:
@
gather empty === return []
@

'pure' (or 'return') constructs singleton lists:
@
gather (pure a) === return [a]
@

'<|>' fills the role of '<>' or '++':
@
gather (pure a <|> pure b) === return [a, b]
@

If we think of '<|>' an addition, then '<*>' is multiplication, and distributes
as such:
@
gather ((pure f <|> pure g) <*> (pure a <|> pure b))
===
return [f a, f b, g a, g b]
@

 -}
newtype ListT m a =
    ListT
        { foldListT
            :: forall r
            .  (a -> m r -> m r)
            -> m r
            -> m r
        }
    deriving (Typeable)

instance Functor (ListT m) where
    fmap f as = ListT $ \yield -> foldListT as (yield . f)
    {-# INLINE fmap #-}

instance Applicative (ListT m) where
    pure a = ListT $ \yield -> yield a
    {-# INLINE pure #-}

    (<*>) fs as =
        ListT $ \yield -> foldListT fs $ \f -> foldListT as $ \a -> yield (f a)
    {-# INLINE (<*>) #-}

instance Alternative (ListT f) where
    empty = ListT $ \_ next -> next
    {-# INLINE empty #-}

    (<|>) as bs =
        ListT $ \yield -> foldListT as yield . foldListT bs yield
    {-# INLINE (<|>) #-}

instance Monad (ListT m) where
    return = pure
    {-# INLINE return #-}

    (>>=) as k =
        ListT $ \yield -> foldListT as $ \a -> foldListT (k a) yield
    {-# INLINE (>>=) #-}

instance Monad m => MonadPlus (ListT m)

instance MonadTrans ListT where
    lift m = ListT $ \yield next -> m >>= \a -> yield a next
    {-# INLINE lift #-}

instance MonadReader r m => MonadReader r (ListT m) where
    ask = lift ask
    {-# INLINE ask #-}

    reader f = lift (reader f)
    {-# INLINE reader #-}

    local f = mapListT (local f)
    {-# INLINE local #-}

instance MonadState s m => MonadState s (ListT m) where
    get = lift get
    {-# INLINE get #-}

    put s = lift (put s)
    {-# INLINE put #-}

    state f = lift (state f)
    {-# INLINE state #-}

instance MonadIO m => MonadIO (ListT m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}

instance (Monad f, Foldable f) => Foldable (ListT f) where
    foldMap f as =
        fold $ foldListT as (\a r -> mappend (f a) <$> r) (pure mempty)
    {-# INLINE foldMap #-}

cons :: a -> ListT m a -> ListT m a
cons a as = ListT $ \yield -> yield a . foldListT as yield
{-# INLINE cons #-}

{- | Collect all values produced by a @'ListT' m@ as a list in @m@.
 -}
gather :: Monad m => ListT m a -> m [a]
gather as = foldListT as (\a mr -> (a :) <$> mr) (pure [])
{-# INLINE gather #-}

{- | Distribute a 'Foldable' collection of values as a @'ListT' m@ stream.

Usually, @f ~ []@.

 -}
scatter :: Foldable f => f a -> ListT m a
scatter = foldr cons empty
{-# INLINE scatter #-}

{- | Apply a transformation of the 'Monad' @m@ underlying @'ListT' m@.

The transformation is applied to the entire list, i.e. given

@
mapListT (\during -> before >> during >> after)
@

the actions @before@ and @after@ are sequenced before and after evaluating the
contents of the list, respectively.

 -}
mapListT :: Monad m => (forall x. m x -> m x) -> ListT m a -> ListT m a
mapListT mapping as = (lift . mapping) (gather as) >>= scatter
