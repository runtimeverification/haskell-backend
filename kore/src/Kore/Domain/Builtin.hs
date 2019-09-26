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
    , InternalAc (..)
    , NormalizedAc (..)
    , emptyNormalizedAc
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
    , InternalInt (..)
    , InternalBool (..)
    , InternalString (..)
    , Domain (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Control.Lens as Lens
import Control.Lens.Iso
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Foldable as Foldable
import Data.Hashable
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Sequence
    ( Seq
    )
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( (<+>)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Class
import Kore.Internal.Symbol
import Kore.Syntax
import Kore.Unparser

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
    \case
        [] -> applyUnit
        xs -> foldr1 applyConcat xs
  where
    applyUnit = unparse unitSymbol <> noArguments
    applyConcat set1 set2 = unparse concatSymbol <> arguments' [set1, set2]

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
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (InternalList child)

instance SOP.HasDatatypeInfo (InternalList child)

instance Debug child => Debug (InternalList child)

instance (Debug child, Diff child) => Diff (InternalList child)

instance Hashable child => Hashable (InternalList child) where
    hashWithSalt salt builtin =
        hashWithSalt salt (Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtin

instance NFData child => NFData (InternalList child)

instance Unparse child => Unparse (InternalList child) where
    unparse builtinList =
        unparseConcat
            builtinListUnit
            builtinListConcat
            (element <$> Foldable.toList builtinListChild)
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
            (element <$> Foldable.toList builtinListChild)
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
data NormalizedAc (collection :: * -> * -> *) key child = NormalizedAc
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

{- | Internal representation of associative-commutative builtin terms.
-}
data InternalAc key (normalized :: * -> * -> *) child =
    InternalAc
        { builtinAcSort :: !Sort
        , builtinAcUnit :: !Symbol
        , builtinAcElement :: !Symbol
        , builtinAcConcat :: !Symbol
        , builtinAcChild :: normalized key child
        }
    deriving (Eq, Foldable, Functor, Traversable, GHC.Generic, Ord, Show)

{- | Establishes a bijection between value wrappers and entire-structure
wrappers, with a few utility functions for the two.
-}
class AcWrapper (normalized :: * -> * -> *) where
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

unwrapElement
    :: AcWrapper normalized
    => Element normalized child -> (child, Value normalized child)
unwrapElement = Lens.view elementIso

wrapElement
    :: AcWrapper normalized
    => (child, Value normalized child) -> Element normalized child
wrapElement = Lens.review elementIso

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

instance SOP.Generic (InternalAc key normalized child)

instance SOP.HasDatatypeInfo (InternalAc key normalized child)

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

instance Hashable child => Hashable (MapValue child) where
    hashWithSalt salt (MapValue child) = hashWithSalt salt child

instance NFData child => NFData (MapValue child)

instance SOP.Generic (MapValue child)

instance SOP.HasDatatypeInfo (MapValue child)

instance Debug child => Debug (MapValue child)

{- | Wrapper for map elements.
 -}
type MapElement = Element NormalizedMap

instance Hashable child => Hashable (MapElement child) where
    hashWithSalt salt (MapElement child) = hashWithSalt salt child

instance NFData child => NFData (MapElement child)

instance SOP.Generic (MapElement child)

instance SOP.HasDatatypeInfo (MapElement child)

instance Debug child => Debug (MapElement child)

{- | Wrapper for normalized maps, to be used in the `builtinAcChild` field.
-}
newtype NormalizedMap key child =
    NormalizedMap {getNormalizedMap :: NormalizedAc NormalizedMap key child}
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance (Hashable key, Hashable child) => Hashable (NormalizedMap key child)
  where
    hashWithSalt salt (NormalizedMap m) = hashWithSalt salt m

instance (NFData key, NFData child) => NFData (NormalizedMap key child)

instance SOP.Generic (NormalizedMap key child)

instance SOP.HasDatatypeInfo (NormalizedMap key child)

instance (Debug key, Debug child) => Debug (NormalizedMap key child)

instance
    ( Debug key, Debug child, Diff key, Diff child )
    => Diff (NormalizedMap key child)

instance AcWrapper NormalizedMap where
    newtype Value NormalizedMap child = MapValue { getMapValue :: child }
        deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

    newtype Element NormalizedMap child =
        MapElement { getMapElement :: (child, child) }
        deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

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

instance (Debug child, Diff child) => Diff (Element NormalizedMap child)

instance (Debug child, Diff child) => Diff (Value NormalizedMap child)

{- | Internal representation of the builtin @MAP.Map@ domain.
-}
type InternalMap key child = InternalAc key NormalizedMap child

-- * Builtin Set

{- | Wrapper for set values, i.e. a wrapper which does not allow any value
for a given key.
-}
type SetValue = Value NormalizedSet

instance Hashable (SetValue child) where
    hashWithSalt salt SetValue = hashWithSalt salt (0 :: Int)

instance NFData (SetValue child)

instance SOP.Generic (SetValue child)

instance SOP.HasDatatypeInfo (SetValue child)

instance Debug (SetValue child)

{- | Wrapper for set elements.
-}
type SetElement = Element NormalizedSet

instance Hashable child => Hashable (SetElement child) where
    hashWithSalt salt (SetElement key) = hashWithSalt salt key

instance NFData child => NFData (SetElement child)

instance SOP.Generic (SetElement child)

instance SOP.HasDatatypeInfo (SetElement child)

instance Debug child => Debug (SetElement child)

{- | Wrapper for normalized sets, to be used in the `builtinAcChild` field.
-}
newtype NormalizedSet key child =
    NormalizedSet { getNormalizedSet :: NormalizedAc NormalizedSet key child }
    deriving (Eq, Foldable, Functor, Traversable, GHC.Generic, Ord, Show)

instance (Hashable key, Hashable child) => Hashable (NormalizedSet key child)
  where
    hashWithSalt salt (NormalizedSet set) =
        hashWithSalt salt set

instance (NFData key, NFData child) => NFData (NormalizedSet key child)

instance SOP.Generic (NormalizedSet key child)

instance SOP.HasDatatypeInfo (NormalizedSet key child)

instance (Debug key, Debug child) => Debug (NormalizedSet key child)

instance
    ( Debug key, Debug child, Diff key, Diff child )
    => Diff (NormalizedSet key child)

instance AcWrapper NormalizedSet where
    data Value NormalizedSet child = SetValue
        deriving (Eq, Foldable, Functor, Traversable, GHC.Generic, Ord, Show)

    newtype Element NormalizedSet child =
        SetElement { getSetElement :: child }
        deriving (Eq, Foldable, Functor, Traversable, GHC.Generic, Ord, Show)

    wrapAc = NormalizedSet
    unwrapAc = getNormalizedSet
    alignValues _ _ = SetValue

    elementIso = Lens.iso (flip (,) SetValue . getSetElement) (SetElement . fst)

    unparseElement childUnparser (SetElement key) =
        argument' (childUnparser key)
    unparseConcreteElement keyUnparser _childUnparser (key, SetValue) =
        argument' (keyUnparser key)

instance (Debug child, Diff child) => Diff (Element NormalizedSet child)

instance Diff child => Diff (Value NormalizedSet child)

{- | Internal representation of the builtin @SET.Set@ domain.
 -}
type InternalSet key child = InternalAc key NormalizedSet child

-- * Builtin Int

{- | Internal representation of the builtin @INT.Int@ domain.
 -}
data InternalInt =
    InternalInt
        { builtinIntSort :: !Sort
        , builtinIntValue :: !Integer
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalInt

instance NFData InternalInt

instance SOP.Generic InternalInt

instance SOP.HasDatatypeInfo InternalInt

instance Debug InternalInt

instance Diff InternalInt

instance Unparse InternalInt where
    unparse InternalInt { builtinIntSort, builtinIntValue } =
        "\\dv"
        <> parameters [builtinIntSort]
        <> arguments' [Pretty.dquotes $ Pretty.pretty builtinIntValue]

    unparse2 InternalInt { builtinIntSort, builtinIntValue } =
        "\\dv2"
        <> parameters2 [builtinIntSort]
        <> arguments' [Pretty.dquotes $ Pretty.pretty builtinIntValue]

-- * Builtin Bool

{- | Internal representation of the builtin @BOOL.Bool@ domain.
 -}
data InternalBool =
    InternalBool
        { builtinBoolSort :: !Sort
        , builtinBoolValue :: !Bool
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalBool

instance NFData InternalBool

instance SOP.Generic InternalBool

instance SOP.HasDatatypeInfo InternalBool

instance Debug InternalBool

instance Diff InternalBool

instance Unparse InternalBool where
    unparse InternalBool { builtinBoolSort, builtinBoolValue } =
        "\\dv"
        <> parameters [builtinBoolSort]
        <> arguments' [Pretty.dquotes value]
      where
        value
          | builtinBoolValue = "true"
          | otherwise        = "false"

    unparse2 InternalBool { builtinBoolSort, builtinBoolValue } =
        "\\dv2"
        <> parameters2 [builtinBoolSort]
        <> arguments' [Pretty.dquotes value]
      where
        value
          | builtinBoolValue = "true"
          | otherwise        = "false"

-- * Builtin String

{- | Internal representation of the builtin @STRING.String@ domain.
 -}
data InternalString =
    InternalString
        { internalStringSort :: !Sort
        , internalStringValue :: !Text
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalString

instance NFData InternalString

instance SOP.Generic InternalString

instance SOP.HasDatatypeInfo InternalString

instance Debug InternalString

instance Diff InternalString

instance Unparse InternalString where
    unparse InternalString { internalStringSort, internalStringValue } =
        "\\dv"
        <> parameters [internalStringSort]
        <> arguments [StringLiteral internalStringValue]

    unparse2 InternalString { internalStringSort, internalStringValue } =
        "\\dv2"
        <> parameters2 [internalStringSort]
        <> arguments2 [StringLiteral internalStringValue]

-- * Builtin domain representations

data Builtin key child
    = BuiltinMap !(InternalMap key child)
    | BuiltinList !(InternalList child)
    | BuiltinSet !(InternalSet key child)
    | BuiltinInt !InternalInt
    | BuiltinBool !InternalBool
    | BuiltinString !InternalString
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance SOP.Generic (Builtin key child)

instance SOP.HasDatatypeInfo (Builtin key child)

instance (Debug key, Debug child) => Debug (Builtin key child)

instance
    (Debug key, Debug child, Diff key, Diff child) => Diff (Builtin key child)

instance (Hashable key, Hashable child) => Hashable (Builtin key child)

instance (NFData key, NFData child) => NFData (Builtin key child)

instance (Unparse key, Unparse child) => Unparse (Builtin key child) where
    unparse evaluated =
        Pretty.sep ["/* builtin: */", unparseGeneric evaluated]
    unparse2 evaluated =
        Pretty.sep ["/* builtin: */", unparse2Generic evaluated]

builtinSort :: Builtin key child -> Sort
builtinSort builtin =
    case builtin of
        BuiltinInt InternalInt { builtinIntSort } -> builtinIntSort
        BuiltinBool InternalBool { builtinBoolSort } -> builtinBoolSort
        BuiltinString InternalString { internalStringSort } ->
            internalStringSort
        BuiltinMap InternalAc { builtinAcSort } -> builtinAcSort
        BuiltinList InternalList { builtinListSort } -> builtinListSort
        BuiltinSet InternalAc { builtinAcSort } -> builtinAcSort

instance Synthetic Sort (Builtin key) where
    synthetic = builtinSort
    {-# INLINE synthetic #-}

instance Ord variable => Synthetic (FreeVariables variable) (Builtin key) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Domain (Builtin key) where
    lensDomainValue mapDomainValue builtin =
        getBuiltin <$> mapDomainValue original
      where
        original =
            DomainValue
                { domainValueChild = builtin
                , domainValueSort = builtinSort builtin
                }
        getBuiltin
            :: forall child
            .  DomainValue Sort (Builtin key child)
            -> Builtin key child
        getBuiltin DomainValue { domainValueSort, domainValueChild } =
            case domainValueChild of
                BuiltinInt internal ->
                    BuiltinInt internal { builtinIntSort = domainValueSort }
                BuiltinBool internal ->
                    BuiltinBool internal { builtinBoolSort = domainValueSort }
                BuiltinString internal ->
                    BuiltinString internal
                        { internalStringSort = domainValueSort }
                BuiltinMap internal ->
                    BuiltinMap internal { builtinAcSort = domainValueSort }
                BuiltinList internal ->
                    BuiltinList internal { builtinListSort = domainValueSort }
                BuiltinSet internal ->
                    BuiltinSet internal { builtinAcSort = domainValueSort }
