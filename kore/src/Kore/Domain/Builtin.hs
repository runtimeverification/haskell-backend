{-|
Module      : Kore.Domain.Builtin
Description : Internal representation of internal domains
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.Domain.Builtin
    ( Builtin (..)
    , builtinSort
    --
    , Element (..)
    , Value (..)
    , AcWrapper (..)
    , wrapElement, unwrapElement
    , wrapConcreteElement
    , InternalAc (..)
    , NormalizedAc (..)
    , nullAc
    , emptyNormalizedAc
    , asSingleOpaqueElem
    , isSymbolicKeyOfAc
    , lookupSymbolicKeyOfAc
    , removeSymbolicKeyOfAc
    , isConcreteKeyOfAc
    , removeConcreteKeyOfAc
    , getSymbolicKeysOfAc
    , getConcreteKeysOfAc
    , getSymbolicValuesOfAc
    , getConcreteValuesOfAc
    --
    , InternalMap
    , MapElement
    , MapValue
    , NormalizedMap (..)
    --
    , InternalSet
    , SetElement
    , SetValue
    , NormalizedSet (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Control.Lens as Lens
import qualified Data.Bifunctor as Bifunctor
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables hiding
    ( toList
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.NormalizedAc
import Kore.Syntax
import Kore.Unparser
import qualified Pretty

-- * Builtin Map

{- | Wrapper for map values.
-}
type MapValue = Value NormalizedMap

{- | Wrapper for map elements.
 -}
type MapElement = Element NormalizedMap

{- | Wrapper for normalized maps, to be used in the `builtinAcChild` field.
-}
newtype NormalizedMap key child =
    NormalizedMap {getNormalizedMap :: NormalizedAc NormalizedMap key child}
    deriving (Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance AcWrapper NormalizedMap where
    newtype Value NormalizedMap child = MapValue { getMapValue :: child }
        deriving (Eq, Ord, Show)
        deriving (Foldable, Functor, Traversable)
        deriving (GHC.Generic)
        deriving anyclass (Hashable, NFData)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)

    newtype Element NormalizedMap child =
        MapElement { getMapElement :: (child, child) }
        deriving (Eq, Ord, Show)
        deriving (Foldable, Functor, Traversable)
        deriving (GHC.Generic)
        deriving anyclass (Hashable, NFData)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)

    wrapAc = NormalizedMap
    unwrapAc = getNormalizedMap
    alignValues (MapValue a) (MapValue b) = MapValue (a, b)

    elementIso =
        Lens.iso
            (Bifunctor.second MapValue . getMapElement)
            (MapElement . Bifunctor.second getMapValue)

    unparseElement childUnparser (MapElement (key, value)) =
        arguments' [childUnparser key, childUnparser value]
    unparseConcreteElement keyUnparser childUnparser (key, MapValue value) =
        arguments' [keyUnparser key, childUnparser value]

{- | Internal representation of the builtin @MAP.Map@ domain.
-}
type InternalMap key child = InternalAc key NormalizedMap child

-- * Builtin Set

{- | Wrapper for set values, i.e. a wrapper which does not allow any value
for a given key.
-}
type SetValue = Value NormalizedSet

{- | Wrapper for set elements.
-}
type SetElement = Element NormalizedSet

{- | Wrapper for normalized sets, to be used in the `builtinAcChild` field.
-}
newtype NormalizedSet key child =
    NormalizedSet { getNormalizedSet :: NormalizedAc NormalizedSet key child }
    deriving (Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance AcWrapper NormalizedSet where
    data Value NormalizedSet child = SetValue
        deriving (Eq, Ord, Show)
        deriving (Foldable, Functor, Traversable)
        deriving (GHC.Generic)
        deriving anyclass (Hashable, NFData)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)

    newtype Element NormalizedSet child =
        SetElement { getSetElement :: child }
        deriving (Eq, Ord, Show)
        deriving (Foldable, Functor, Traversable)
        deriving (GHC.Generic)
        deriving anyclass (Hashable, NFData)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)

    wrapAc = NormalizedSet
    unwrapAc = getNormalizedSet
    alignValues _ _ = SetValue

    elementIso = Lens.iso (flip (,) SetValue . getSetElement) (SetElement . fst)

    unparseElement childUnparser (SetElement key) =
        argument' (childUnparser key)
    unparseConcreteElement keyUnparser _childUnparser (key, SetValue) =
        argument' (keyUnparser key)

{- | Internal representation of the builtin @SET.Set@ domain.
 -}
type InternalSet key child = InternalAc key NormalizedSet child

-- * Builtin domain representations

data Builtin key child
    = BuiltinMap !(InternalMap key child)
    | BuiltinSet !(InternalSet key child)
    deriving (Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance (Unparse key, Unparse child) => Unparse (Builtin key child) where
    unparse evaluated =
        Pretty.sep ["/* builtin: */", unparseGeneric evaluated]
    unparse2 evaluated =
        Pretty.sep ["/* builtin: */", unparse2Generic evaluated]

builtinSort :: Builtin key child -> Sort
builtinSort builtin =
    case builtin of
        BuiltinMap InternalAc { builtinAcSort } -> builtinAcSort
        BuiltinSet InternalAc { builtinAcSort } -> builtinAcSort

instance Synthetic Sort (Builtin key) where
    synthetic = builtinSort
    {-# INLINE synthetic #-}

instance Ord variable => Synthetic (FreeVariables variable) (Builtin key) where
    synthetic = fold
    {-# INLINE synthetic #-}
