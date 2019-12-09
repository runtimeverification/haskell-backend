{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Pair
    ( Pair (..)
    ) where

import qualified GHC.Generics as GHC

{- | A tuple @(a, a)@ where both elements are the same type.
 -}
data Pair a = Pair !a !a
    deriving (Eq, Ord, Read, Show)
    deriving (GHC.Generic)
    deriving (Foldable, Functor, Traversable)
