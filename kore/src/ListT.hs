{-|
Module      : ListT
Description : List monad transformer
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

This module implements the list monad transformer.

-}

module ListT
    ( ListT (..)
    , cons
    , gather
    , scatter
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
            :: forall n r
            .  (forall x y. m x -> (x -> n y) -> n y)
            -- ^ analog of 'bind' to use an @m@-value within @n@; if @m ~ n@
            -- this is literally 'bind'
            -> (a -> n r -> n r)
            -> n r
            -> n r
        }
    deriving (Typeable)

instance Functor (ListT m) where
    fmap f as =
        ListT $ \nbind yield ->
            foldListT as nbind (yield . f)
    {-# INLINE fmap #-}

instance Applicative (ListT m) where
    pure a = ListT $ \_ yield -> yield a
    {-# INLINE pure #-}

    (<*>) fs as =
        ListT $ \nbind yield ->
            foldListT fs nbind $ \f ->
                foldListT as nbind $ \a ->
                    yield (f a)
    {-# INLINE (<*>) #-}

instance Alternative (ListT f) where
    empty = ListT $ \_ _ next -> next
    {-# INLINE empty #-}

    (<|>) as bs =
        ListT $ \nbind yield ->
            foldListT as nbind yield . foldListT bs nbind yield
    {-# INLINE (<|>) #-}

instance Monad (ListT m) where
    return = pure
    {-# INLINE return #-}

    (>>=) as k =
        ListT $ \nbind yield ->
            foldListT as nbind $ \a ->
                foldListT (k a) nbind yield
    {-# INLINE (>>=) #-}

instance MonadPlus (ListT m)

instance MonadTrans ListT where
    lift m = ListT $ \nbind yield next -> nbind m (\a -> yield a next)
    {-# INLINE lift #-}

instance MFunctor ListT where
    hoist morph bs = ListT $ \nbind -> foldListT bs (nbind . morph)
    {-# INLINE hoist #-}

instance MMonad ListT where
    embed mlift bs = foldListT bs ((>>=) . mlift) cons empty
    {-# INLINE embed #-}

instance MonadReader r m => MonadReader r (ListT m) where
    ask = lift ask
    {-# INLINE ask #-}

    reader f = lift (reader f)
    {-# INLINE reader #-}

    local f = hoist (local f)
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
        fold $ foldListT as (>>=) (\a r -> mappend (f a) <$> r) (pure mempty)
    {-# INLINE foldMap #-}

cons :: a -> ListT m a -> ListT m a
cons a as = ListT $ \nbind yield -> yield a . foldListT as nbind yield
{-# INLINE cons #-}

{- | Collect all values produced by a @'ListT' m@ as a list in @m@.
 -}
gather :: Monad m => ListT m a -> m [a]
gather as = foldListT as (>>=) (\a mr -> (a :) <$> mr) (pure [])
{-# INLINE gather #-}

{- | Distribute a 'Foldable' collection of values as a @'ListT' m@ stream.

Usually, @f ~ []@.

 -}
scatter :: Foldable f => f a -> ListT m a
scatter = foldr cons empty
{-# INLINE scatter #-}
