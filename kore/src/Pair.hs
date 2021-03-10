{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Pair (
    Pair (..),
) where

import Prelude.Kore

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP

import Debug

-- | A tuple @(a, a)@ where both elements are the same type.
data Pair a = Pair !a !a
    deriving (Eq, Ord, Read, Show)
    deriving (GHC.Generic)
    deriving (Foldable, Functor, Traversable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
