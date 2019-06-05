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
            :: forall n r
            .  Monad n
            => (forall x. m x -> n x)
            -> (m a -> n r -> n r)
            -> n r
            -> n r
        }
    deriving (Typeable)

instance Functor f => Functor (ListT f) where
    fmap f as =
        ListT $ \nlift yield ->
            foldListT as nlift (yield . fmap f)
    {-# INLINE fmap #-}

instance Applicative f => Applicative (ListT f) where
    pure a = ListT $ \_ yield -> yield (pure a)
    {-# INLINE pure #-}

    (<*>) fs as =
        ListT $ \nlift yield ->
            foldListT fs nlift $ \ff ->
                foldListT as nlift $ \fa ->
                    yield (ff <*> fa)
    {-# INLINE (<*>) #-}

instance Applicative f => Alternative (ListT f) where
    empty = ListT $ \_ _ next -> next
    {-# INLINE empty #-}

    (<|>) as bs =
        ListT $ \nlift yield ->
            foldListT as nlift yield . foldListT bs nlift yield
    {-# INLINE (<|>) #-}

instance Monad m => Monad (ListT m) where
    return = pure
    {-# INLINE return #-}

    (>>=) as k =
        ListT $ \nlift yield ->
            foldListT as nlift $ \ma nr ->
                nlift ma >>= \a -> foldListT (k a) nlift yield nr
    {-# INLINE (>>=) #-}

instance Monad m => MonadPlus (ListT m)

instance MonadTrans ListT where
    lift ma = ListT $ \_ yield -> yield ma
    {-# INLINE lift #-}

instance MFunctor ListT where
    hoist morph bs = ListT $ \nlift yield next ->
        foldListT bs (nlift . morph) (yield . morph) next
    {-# INLINE hoist #-}

-- instance MMonad ListT where
--     embed mlift bs =
--         -- foldListT bs ((>>=) . mlift) cons empty
--         ListT $ \nlift yield next ->
--             foldListT bs (nlift . _) _ _
--     {-# INLINE embed #-}

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
        fold $ foldListT as id (\fa fr -> mappend <$> (f <$> fa) <*> fr) (pure mempty)
    {-# INLINE foldMap #-}

cons :: Applicative m => a -> ListT m a -> ListT m a
cons a as = ListT $ \nlift yield -> yield (pure a) . foldListT as nlift yield
{-# INLINE cons #-}

{- | Collect all values produced by a @'ListT' m@ as a list in @m@.
 -}
gather :: Monad m => ListT m a -> m [a]
gather as = foldListT as id (\ma mr -> (:) <$> ma <*> mr) (pure [])
{-# INLINE gather #-}

{- | Distribute a 'Foldable' collection of values as a @'ListT' m@ stream.

Usually, @f ~ []@.

 -}
scatter :: (Applicative m, Foldable f) => f a -> ListT m a
scatter = foldr cons empty
{-# INLINE scatter #-}
