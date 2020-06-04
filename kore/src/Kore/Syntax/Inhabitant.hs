{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Inhabitant
    ( Inhabitant (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , emptyFreeVariables
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

-- | 'Inhabitant' symbolizes the inhabitants of a sort.
newtype Inhabitant child = Inhabitant { inhSort :: Sort }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance Hashable (Inhabitant child)

instance NFData (Inhabitant child)

instance SOP.Generic (Inhabitant child)

instance SOP.HasDatatypeInfo (Inhabitant child)

instance Debug (Inhabitant child)

instance Diff (Inhabitant child)

instance Unparse (Inhabitant child) where
    unparse = unparse . inhSort
    unparse2 = unparse2 . inhSort

instance Synthetic (FreeVariables variable) Inhabitant where
    synthetic = const emptyFreeVariables
    {-# INLINE synthetic #-}

instance Synthetic Sort Inhabitant where
    synthetic = inhSort
    {-# INLINE synthetic #-}
