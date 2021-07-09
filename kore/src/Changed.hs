{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Changed (
    Changed (..),
    getChanged,
) where

import Prelude.Kore

-- | @'Changed' thing@ carries a @thing@ and a marker.
data Changed thing
    = -- | The @thing@ was not changed.
      Unchanged !thing
    | -- | The @thing@ was changed.
      Changed !thing
    deriving stock (Eq, Functor, Show)

instance Applicative Changed where
    pure = Unchanged

    Unchanged f <*> a = fmap f a
    Changed f <*> a = Changed (f $ extract a)

instance Comonad Changed where
    extract (Unchanged a) = a
    extract (Changed a) = a

    extend f changed@(Unchanged _) = Unchanged (f changed)
    extend f changed@(Changed _) = Changed (f changed)

    duplicate changed@(Unchanged _) = Unchanged changed
    duplicate changed@(Changed _) = Changed changed

instance Monad Changed where
    Unchanged a >>= f = f a
    Changed a >>= f = Changed $ extract $ f a

getChanged :: Changed a -> Maybe a
getChanged (Changed a) = Just a
getChanged (Unchanged _) = Nothing
