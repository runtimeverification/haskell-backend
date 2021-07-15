{- |
Module      : Data.Limit
Description : Optionally-limited quantities
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
This module is intended to be imported qualified:
@
import Data.Limit ( Limit (..) )
import qualified Data.Limit as Limit
@
-}
module Data.Limit (
    Limit (..),
    enumFromLimit,
    maybeLimit,
    replicate,
    takeWithin,
    withinLimit,
) where

import Prelude.Kore hiding (
    replicate,
 )

-- | An optionally-limited quantity.
data Limit a
    = -- | No limit
      Unlimited
    | -- | Limit @a@ by the given (inclusive) upper bound
      Limit !a
    deriving stock (Eq, Read, Show, Foldable)

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

-- | Is the given value within the (inclusive) upper bound?
withinLimit :: Ord a => Limit a -> a -> Bool
withinLimit =
    \case
        Unlimited -> const True
        Limit u -> (<= u)

-- | Enumerate values beginning at @a@ and within the limit.
enumFromLimit :: (Enum a, Ord a) => Limit a -> a -> [a]
enumFromLimit limit a = takeWhile (withinLimit limit) (enumFrom a)

{- | A list of limited length with identical elements.

@replicate Unlimited x@ is an infinite list where @x@ is the value of every
element.

@replicate (Limit n) x@ is a list of length @n@ where @x@ is the value of every
element.
-}
replicate :: (Enum a, Ord a) => Limit a -> b -> [b]
replicate limit b = takeWithin limit (repeat b)

-- | Take a limited prefix of the given list.
takeWithin :: (Enum a, Ord a) => Limit a -> [b] -> [b]
takeWithin limit bs = zipWith const bs limiting
  where
    limiting = enumFromLimit limit (toEnum 1)

maybeLimit :: b -> (a -> b) -> Limit a -> b
maybeLimit b f = foldr (\a _ -> f a) b
