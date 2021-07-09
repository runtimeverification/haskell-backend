{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Inhabitant (
    Inhabitant (..),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    emptyFreeVariables,
 )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Prelude.Kore

-- | 'Inhabitant' symbolizes the inhabitants of a sort.
newtype Inhabitant child = Inhabitant {inhSort :: Sort}
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse (Inhabitant child) where
    unparse = unparse . inhSort
    unparse2 = unparse2 . inhSort

instance Synthetic (FreeVariables variable) Inhabitant where
    synthetic = const emptyFreeVariables
    {-# INLINE synthetic #-}

instance Synthetic Sort Inhabitant where
    synthetic = inhSort
    {-# INLINE synthetic #-}
