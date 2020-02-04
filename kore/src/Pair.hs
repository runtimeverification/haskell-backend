{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Pair
    ( Pair (..)
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug

{- | A tuple @(a, a)@ where both elements are the same type.
 -}
data Pair a = Pair !a !a
    deriving (Eq, Ord, Read, Show)
    deriving (GHC.Generic)
    deriving (Foldable, Functor, Traversable)

instance SOP.Generic (Pair a)

instance SOP.HasDatatypeInfo (Pair a)

instance Debug a => Debug (Pair a)

instance (Debug a, Diff a) => Diff (Pair a)
