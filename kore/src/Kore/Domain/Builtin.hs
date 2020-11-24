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
    , InternalList (..)
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
    --
    , InternalString (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Control.Lens as Lens
import Control.Lens.Iso
    ( Iso'
    )
import qualified Data.Bifunctor as Bifunctor
import Data.Kind
    ( Type
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Sequence
    ( Seq
    )
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables hiding
    ( toList
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.Symbol
import Kore.Syntax
import Kore.Unparser
import Pretty
    ( (<+>)
    )
import qualified Pretty

-- * Helpers

{- | Unparse a concatenation of elements, given the @unit@ and @concat@ symbols.

The children are already unparsed. If they are @element@s of the collection,
they are wrapped by the @element@ symbol.

 -}
unparseConcat
    :: Symbol  -- ^ unit symbol
    -> Symbol  -- ^ concat symbol
    -> [Pretty.Doc ann]      -- ^ children
    -> Pretty.Doc ann
unparseConcat unitSymbol concatSymbol =
    unparseAssoc' (unparse concatSymbol) applyUnit
  where
    applyUnit = unparse unitSymbol <> noArguments

-- * Builtin List

{- | Internal representation of the builtin @LIST.List@ domain.
 -}
data InternalList child =
    InternalList
        { builtinListSort :: !Sort
        , builtinListUnit :: !Symbol
        , builtinListElement :: !Symbol
        , builtinListConcat :: !Symbol
        , builtinListChild :: !(Seq child)
        }
    deriving (Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Hashable child => Hashable (InternalList child) where
    hashWithSalt salt builtin =
        hashWithSalt salt (toList builtinListChild)
      where
        InternalList { builtinListChild } = builtin

instance NFData child => NFData (InternalList child)

instance Unparse child => Unparse (InternalList child) where
    unparse builtinList =
        unparseConcat
            builtinListUnit
            builtinListConcat
            (element <$> toList builtinListChild)
      where
        element x = unparse builtinListElement <> arguments [x]
        InternalList { builtinListChild } = builtinList
        InternalList { builtinListUnit } = builtinList
        InternalList { builtinListElement } = builtinList
        InternalList { builtinListConcat } = builtinList

    unparse2 builtinList =
        unparseConcat
            builtinListUnit
            builtinListConcat
            (element <$> toList builtinListChild)
      where
        element x = unparse2 builtinListElement <> arguments2 [x]
        InternalList { builtinListChild } = builtinList
        InternalList { builtinListUnit } = builtinList
        InternalList { builtinListElement } = builtinList
        InternalList { builtinListConcat } = builtinList

-- * Builtin AC (associative-commutative) generic stuff

{- | Internal representation for associative-commutative domain values.

The valueWrapper is a data type holding the non-key part of elements.
For a set, the valueWapper would be something equivalent to @Data.Empty.T@.
For a map, it would be something equivalent to @Identity@.
-}
data NormalizedAc (collection :: Type -> Type -> Type) key child = NormalizedAc
    { elementsWithVariables :: [Element collection child]
    -- ^ Non-concrete elements of the structure.
    -- These would be of sorts @(Int, String)@ for a map from @Int@ to @String@.
    , concreteElements :: Map key (Value collection child)
    -- ^ Concrete elements of the structure.
    -- These would be of sorts @(Int, String)@ for a map from @Int@ to @String@.
    , opaque :: [child]
    -- ^ Unoptimized (i.e. non-element) parts of the structure.
    }
    deriving (GHC.Generic)

nullAc :: NormalizedAc normalized key child -> Bool
nullAc normalizedAc =
    null (elementsWithVariables normalizedAc)
    && null (concreteElements normalizedAc)
    && null (opaque normalizedAc)

isSymbolicKeyOfAc
    :: AcWrapper normalized
    => Eq child
    => child
    -> normalized key child
    -> Bool
isSymbolicKeyOfAc child normalized =
    child `elem` getSymbolicKeysOfAc normalized

getSymbolicKeysOfAc
    :: AcWrapper normalized
    => normalized key child
    -> [child]
getSymbolicKeysOfAc
    ( unwrapAc ->
        NormalizedAc { elementsWithVariables }
    )
  =
    fst . unwrapElement <$> elementsWithVariables

getSymbolicValuesOfAc
    :: AcWrapper normalized
    => normalized key child
    -> [Value normalized child]
getSymbolicValuesOfAc
    ( unwrapAc ->
        NormalizedAc { elementsWithVariables }
    )
  =
    snd . unwrapElement <$> elementsWithVariables

lookupSymbolicKeyOfAc
    :: AcWrapper normalized
    => Eq child
    => child
    -> NormalizedAc normalized key child
    -> Maybe (Value normalized child)
lookupSymbolicKeyOfAc
    child
    NormalizedAc { elementsWithVariables }
  =
    snd <$> find (\(key, _) -> child == key) elements
  where
    elements = unwrapElement <$> elementsWithVariables

removeSymbolicKeyOfAc
    :: AcWrapper normalized
    => Ord child
    => child
    -> NormalizedAc normalized key child
    -> NormalizedAc normalized key child
removeSymbolicKeyOfAc
    child
    normalized@NormalizedAc { elementsWithVariables }
  =
    normalized
        { elementsWithVariables =
            fmap wrapElement . Map.toList
            $ Map.delete child unwrappedMap
        }
  where
    unwrappedMap =
        Map.fromList $ fmap unwrapElement elementsWithVariables

isConcreteKeyOfAc
    :: AcWrapper normalized
    => Ord key
    => key
    -> normalized key child
    -> Bool
isConcreteKeyOfAc key normalized =
    key `elem` getConcreteKeysOfAc normalized

getConcreteKeysOfAc
    :: AcWrapper normalized
    => normalized key child
    -> [key]
getConcreteKeysOfAc
    ( unwrapAc ->
        NormalizedAc { concreteElements }
    )
  =
    Map.keys concreteElements

getConcreteValuesOfAc
    :: AcWrapper normalized
    => normalized key child
    -> [Value normalized child]
getConcreteValuesOfAc
    ( unwrapAc ->
        NormalizedAc { concreteElements }
    )
  =
    Map.elems concreteElements

removeConcreteKeyOfAc
    :: Ord key
    => key
    -> NormalizedAc normalized key child
    -> NormalizedAc normalized key child
removeConcreteKeyOfAc
    key
    normalized@NormalizedAc { concreteElements }
  =
    normalized
        { concreteElements =
            Map.delete key concreteElements
        }

deriving instance
    ( Eq key, Eq child
    , Eq (Element collection child), Eq (Value collection child)
    )
    => Eq (NormalizedAc collection key child)

deriving instance
    ( Ord key, Ord child
    , Ord (Element collection child), Ord (Value collection child)
    )
    => Ord (NormalizedAc collection key child)

deriving instance
    ( Show key, Show child
    , Show (Element collection child), Show (Value collection child)
    )
    => Show (NormalizedAc collection key child)

deriving instance
    (Functor (Element collection), Functor (Value collection)) =>
    Functor (NormalizedAc collection key)

deriving instance
    (Foldable (Element collection), Foldable (Value collection)) =>
    Foldable (NormalizedAc collection key)

deriving instance
    (Traversable (Element collection), Traversable (Value collection)) =>
    Traversable (NormalizedAc collection key)

instance
    ( Hashable key, Hashable child
    , Hashable (Element collection child), Hashable (Value collection child)
    )
    => Hashable (NormalizedAc collection key child)
  where
    hashWithSalt salt normalized@(NormalizedAc _ _ _) =
        salt
            `hashWithSalt` elementsWithVariables
            `hashWithSalt` Map.toList concreteElements
            `hashWithSalt` opaque
      where
        NormalizedAc { elementsWithVariables } = normalized
        NormalizedAc { concreteElements } = normalized
        NormalizedAc { opaque } = normalized

instance
    ( NFData key, NFData child
    , NFData (Element collection child), NFData (Value collection child)
    )
    => NFData (NormalizedAc collection key child)

instance SOP.Generic (NormalizedAc key valueWrapper child)

instance SOP.HasDatatypeInfo (NormalizedAc key valueWrapper child)

instance
    ( Debug key, Debug child
    , Debug (Element collection child), Debug (Value collection child)
    )
    => Debug (NormalizedAc collection key child)

instance
    ( Debug key, Debug child
    , Debug (Element collection child), Debug (Value collection child)
    , Diff key, Diff child
    , Diff (Element collection child), Diff (Value collection child)
    )
    => Diff (NormalizedAc collection key child)

emptyNormalizedAc :: NormalizedAc key valueWrapper child
emptyNormalizedAc = NormalizedAc
    { elementsWithVariables = []
    , concreteElements = Map.empty
    , opaque = []
    }

asSingleOpaqueElem
    :: NormalizedAc key valueWrapper child
    -> Maybe child
asSingleOpaqueElem
    NormalizedAc
        { elementsWithVariables
        , concreteElements
        , opaque
        }
    | null elementsWithVariables
    , null concreteElements
    , [singleOpaqueElem] <- opaque
  =
      Just singleOpaqueElem
    | otherwise =  Nothing

{- | Internal representation of associative-commutative builtin terms.
-}
data InternalAc key (normalized :: Type -> Type -> Type) child =
    InternalAc
        { builtinAcSort :: !Sort
        , builtinAcUnit :: !Symbol
        , builtinAcElement :: !Symbol
        , builtinAcConcat :: !Symbol
        , builtinAcChild :: normalized key child
        }
    deriving (Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

{- | Establishes a bijection between value wrappers and entire-structure
wrappers, with a few utility functions for the two.
-}
class AcWrapper (normalized :: Type -> Type -> Type) where
    -- TODO (thomas.tuegel): Make this a type family?
    data family Value normalized child
    data family Element normalized child

    unwrapAc :: normalized key child -> NormalizedAc normalized key child
    wrapAc :: NormalizedAc normalized key child -> normalized key child

    {-| Pairs the values in two wrappers as they should be paired for
    unification.
    -}
    alignValues
        :: Value normalized a
        -> Value normalized b
        -> Value normalized (a, b)

    elementIso
        :: Iso' (Element normalized child) (child, Value normalized child)

    unparseElement
        :: (child -> Pretty.Doc ann)
        -> Element normalized child -> Pretty.Doc ann

    unparseConcreteElement
        :: (key -> Pretty.Doc ann)
        -> (child -> Pretty.Doc ann)
        -> (key, Value normalized child) -> Pretty.Doc ann

instance
    (AcWrapper normalized, From key child)
    => From (key, Value normalized child) (Element normalized child)
  where
    from (key, value) = wrapElement (from @key @child key, value)

unwrapElement
    :: AcWrapper normalized
    => Element normalized child -> (child, Value normalized child)
unwrapElement = Lens.view elementIso

wrapElement
    :: AcWrapper normalized
    => (child, Value normalized child) -> Element normalized child
wrapElement = Lens.review elementIso

wrapConcreteElement
    :: AcWrapper normalized
    => From key child
    => (key, Value normalized child) -> Element normalized child
wrapConcreteElement = from

unparsedChildren
    :: forall ann child key normalized
    .  AcWrapper normalized
    => Symbol
    -> (key -> Pretty.Doc ann)
    -> (child -> Pretty.Doc ann)
    -> normalized key child
    -> [Pretty.Doc ann]
unparsedChildren elementSymbol keyUnparser childUnparser wrapped =
    (elementUnparser <$> elementsWithVariables)
    ++ (concreteElementUnparser <$> Map.toAscList concreteElements)
    ++ (child . childUnparser <$> opaque)
  where
    unwrapped :: NormalizedAc normalized key child
    -- Matching needed only for getting compiler notifications when
    -- the NormalizedAc field count changes.
    unwrapped@(NormalizedAc _ _ _) = unwrapAc wrapped

    NormalizedAc {elementsWithVariables} = unwrapped
    NormalizedAc {concreteElements} = unwrapped
    NormalizedAc {opaque} = unwrapped
    element = (<>) ("/* element: */" <+> unparse elementSymbol)
    concreteElement = (<>) ("/* concrete element: */" <+> unparse elementSymbol)
    child = (<+>) "/* opaque child: */"

    elementUnparser :: Element normalized child -> Pretty.Doc ann
    elementUnparser = element . unparseElement childUnparser

    concreteElementUnparser :: (key, Value normalized child) -> Pretty.Doc ann
    concreteElementUnparser =
        concreteElement . unparseConcreteElement keyUnparser childUnparser

instance Hashable (normalized key child)
    => Hashable (InternalAc key normalized child)
  where
    hashWithSalt salt builtin =
        hashWithSalt salt builtinAcChild
      where
        InternalAc { builtinAcChild } = builtin

instance (NFData (normalized key child))
    => NFData (InternalAc key normalized child)

instance (Debug (normalized key child))
    => Debug (InternalAc key normalized child)

instance
    (Debug (normalized key child), Diff (normalized key child))
    => Diff (InternalAc key normalized child)

instance
    ( Unparse key
    , Unparse child
    , AcWrapper normalized
    )
    => Unparse (InternalAc key normalized child)
  where
    unparse = unparseInternalAc unparse unparse
    unparse2 = unparseInternalAc unparse2 unparse2

unparseInternalAc
    :: (AcWrapper normalized)
    => (key -> Pretty.Doc ann)
    -> (child -> Pretty.Doc ann)
    -> InternalAc key normalized child
    -> Pretty.Doc ann
unparseInternalAc keyUnparser childUnparser builtinAc =
    unparseConcat builtinAcUnit builtinAcConcat
    $ unparsedChildren builtinAcElement keyUnparser childUnparser builtinAcChild
  where
    InternalAc { builtinAcChild } = builtinAc
    InternalAc { builtinAcUnit } = builtinAc
    InternalAc { builtinAcElement } = builtinAc
    InternalAc { builtinAcConcat } = builtinAc

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

-- * Builtin Bool

-- * Builtin String

{- | Internal representation of the builtin @STRING.String@ domain.
 -}
data InternalString =
    InternalString
        { internalStringSort :: !Sort
        , internalStringValue :: !Text
        }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse InternalString where
    unparse InternalString { internalStringSort, internalStringValue } =
        "\\dv"
        <> parameters [internalStringSort]
        <> Pretty.parens (unparse $ StringLiteral internalStringValue)

    unparse2 InternalString { internalStringSort, internalStringValue } =
        "\\dv2"
        <> parameters2 [internalStringSort]
        <> arguments2 [StringLiteral internalStringValue]

-- * Builtin domain representations

data Builtin key child
    = BuiltinMap !(InternalMap key child)
    | BuiltinList !(InternalList child)
    | BuiltinSet !(InternalSet key child)
    | BuiltinString !InternalString
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
        BuiltinString InternalString { internalStringSort } ->
            internalStringSort
        BuiltinMap InternalAc { builtinAcSort } -> builtinAcSort
        BuiltinList InternalList { builtinListSort } -> builtinListSort
        BuiltinSet InternalAc { builtinAcSort } -> builtinAcSort

instance Synthetic Sort (Builtin key) where
    synthetic = builtinSort
    {-# INLINE synthetic #-}

instance Ord variable => Synthetic (FreeVariables variable) (Builtin key) where
    synthetic = fold
    {-# INLINE synthetic #-}
