{-|
Module      : Data.Limit
Description : Optionally-limited quantities
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Data.Limit
    ( Limit (..)
    , enumFromLimit
    , withinLimit
    ) where

{- | An optionally-limited quantity.
 -}
data Limit a
    = Unlimited
    -- ^ No limit
    | Limit !a
    -- ^ Limit @a@ by the given (inclusive) upper bound
    deriving (Eq, Show)

instance Ord a => Ord (Limit a) where
    compare =
        \case
            Unlimited ->
                \case
                    Unlimited -> EQ
                    Limit _ -> GT
            Limit a ->
                \case
                    Unlimited -> LT
                    Limit b -> compare a b

instance Ord a => Semigroup (Limit a) where
    (<>) = min

instance Ord a => Monoid (Limit a) where
    mempty = Unlimited
    mappend = (<>)

{- | Is the given value within the (inclusive) upper bound?
 -}
withinLimit :: Ord a => Limit a -> a -> Bool
withinLimit =
    \case
        Unlimited -> \_ -> True
        Limit u -> \a -> a <= u

{- | Enumerate values beginning at @a@ and within the limit.
 -}
enumFromLimit :: (Enum a, Ord a) => Limit a -> a -> [a]
enumFromLimit limit a = takeWhile (withinLimit limit) (enumFrom a)
