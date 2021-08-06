{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Internal.InternalSet (
    InternalSet,
    InternalAc (..),
    Element (..),
    SetElement,
    Value (..),
    SetValue,
    NormalizedSet (..),

    -- * Re-exports
    module Kore.Internal.NormalizedAc,
) where

import qualified Control.Lens as Lens
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables hiding (
    toList,
 )
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Pattern.Simplified
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.NormalizedAc
import Kore.Syntax
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

-- * Builtin Set

{- | Wrapper for set values, i.e. a wrapper which does not allow any value
for a given key.
-}
type SetValue = Value NormalizedSet

-- | Wrapper for set elements.
type SetElement = Element NormalizedSet

-- | Wrapper for normalized sets, to be used in the `builtinAcChild` field.
newtype NormalizedSet key child = NormalizedSet {getNormalizedSet :: NormalizedAc NormalizedSet key child}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving stock (Traversable)
    deriving newtype (Foldable, Functor)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance AcWrapper NormalizedSet where
    data Value NormalizedSet child = SetValue
        deriving stock (Eq, Ord, Show)
        deriving stock (Foldable, Functor, Traversable)
        deriving stock (GHC.Generic)
        deriving anyclass (Hashable, NFData)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)

    newtype Element NormalizedSet child = SetElement {getSetElement :: child}
        deriving stock (Eq, Ord, Show)
        deriving stock (Foldable, Functor, Traversable)
        deriving stock (GHC.Generic)
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

-- | Internal representation of the builtin @SET.Set@ domain.
type InternalSet key = InternalAc key NormalizedSet

instance (Unparse key, Unparse child) => Unparse (InternalSet key child) where
    unparse internalMap =
        Pretty.hsep
            [ "/* InternalSet: */"
            , unparseInternalAc unparse unparse internalMap
            ]
    unparse2 internalMap =
        Pretty.hsep
            [ "/* InternalSet: */"
            , unparseInternalAc unparse2 unparse2 internalMap
            ]

instance Synthetic Sort (InternalSet key) where
    synthetic = builtinAcSort
    {-# INLINE synthetic #-}

instance
    HasConstructorLike key =>
    Synthetic ConstructorLike (InternalSet key)
    where
    synthetic InternalAc{builtinAcChild = NormalizedSet builtinSetChild} =
        normalizedAcConstructorLike builtinSetChild
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is defined if its subterms are 'Defined'.
instance Synthetic Defined (InternalSet key) where
    synthetic InternalAc{builtinAcChild = NormalizedSet builtinSetChild} =
        normalizedAcDefined builtinSetChild
    {-# INLINE synthetic #-}

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (InternalSet key)
    where
    synthetic = fold
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is 'Function' if its subterms are 'Function'.
instance Synthetic Function (InternalAc key NormalizedSet) where
    synthetic = fold
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is 'Functional' if its subterms are 'Functional'.
instance Synthetic Functional (InternalAc key NormalizedSet) where
    synthetic InternalAc{builtinAcChild = NormalizedSet builtinSetChild} =
        normalizedAcFunctional builtinSetChild
    {-# INLINE synthetic #-}

instance Synthetic Simplified (InternalAc key NormalizedSet) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance HasConstructorLike (Value NormalizedSet ConstructorLike) where
    extractConstructorLike SetValue =
        ConstructorLike . Just $ ConstructorLikeHead
