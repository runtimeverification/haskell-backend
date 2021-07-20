{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Partial (Partial (..), getPartial) where

import Prelude.Kore

{- | A type for combining results which can be undefined.
 'Bottom' acts as the annihilator to the semigroup operation.
-}
data Partial a = Bottom | Defined a
    deriving stock (Show, Eq, Functor)

instance Semigroup a => Semigroup (Partial a) where
    (<>) Bottom _ = Bottom
    (<>) _ Bottom = Bottom
    (<>) (Defined a) (Defined b) = Defined (a <> b)

instance Monoid a => Monoid (Partial a) where
    mempty = Defined mempty

-- | Attempt to extract a partial value.
getPartial :: Partial a -> Maybe a
getPartial Bottom = Nothing
getPartial (Defined a) = Just a
