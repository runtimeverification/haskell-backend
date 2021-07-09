{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Pair (
    Pair (..),
) where

import Debug
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Prelude.Kore

-- | A tuple @(a, a)@ where both elements are the same type.
data Pair a = Pair !a !a
    deriving stock (Eq, Ord, Read, Show)
    deriving stock (GHC.Generic)
    deriving stock (Foldable, Functor, Traversable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
