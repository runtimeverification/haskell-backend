{-|
Module      : Kore.Domain.Builtin
Description : Internal representation of internal domains
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Domain.Builtin
    ( Builtin (..)
    , builtinSort
    , InternalList (..)
    , lensBuiltinListSort
    , lensBuiltinListUnit
    , lensBuiltinListElement
    , lensBuiltinListConcat
    , lensBuiltinListChild
    , InternalMap
    , NormalizedMap (..)
    , Value (..)
    , InternalSet
    , NormalizedSet (..)
    , NoValue (..)
    , AcWrapper (..)
    , InternalAc (..)
    , NormalizedAc (..)
    , emptyNormalizedAc
    , lensBuiltinAcSort
    , lensBuiltinAcUnit
    , lensBuiltinAcElement
    , lensBuiltinAcConcat
    , lensBuiltinAcChild
    , InternalInt (..)
    , lensBuiltinIntSort
    , lensBuiltinIntValue
    , InternalBool (..)
    , lensBuiltinBoolSort
    , lensBuiltinBoolValue
    , InternalString (..)
    , lensInternalStringSort
    , lensInternalStringValue
    , Domain (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Sequence
                 ( Seq )
import           Data.Text
                 ( Text )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Control.Lens.TH.Rules
       ( makeLenses )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Class
import Kore.Internal.Symbol
import Kore.Syntax
import Kore.Unparser

-- * Helpers

{- | Unparse a builtin collection type, given its symbols and children.

The children are already unparsed.

 -}
unparseCollection
    :: Symbol  -- ^ unit symbol
    -> Symbol  -- ^ element symbol
    -> Symbol  -- ^ concat symbol
    -> [Pretty.Doc ann]      -- ^ children
    -> Pretty.Doc ann
unparseCollection unitSymbol elementSymbol concatSymbol =
    \case
        [] -> applyUnit
        xs -> foldr1 applyConcat (applyElement <$> xs)
  where
    applyUnit = unparse unitSymbol <> noArguments
    applyElement elem' = unparse elementSymbol <> elem'
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

instance Hashable child => Hashable (InternalList child) where
    hashWithSalt salt builtin =
        hashWithSalt salt (Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtin

instance NFData child => NFData (InternalList child)

instance Unparse child => Unparse (InternalList child) where
    unparse builtinList =
        unparseCollection
            builtinListUnit
            builtinListElement
            builtinListConcat
            (argument' . unparse <$> Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtinList
        InternalList { builtinListUnit } = builtinList
        InternalList { builtinListElement } = builtinList
        InternalList { builtinListConcat } = builtinList

    unparse2 builtinList =
        unparseCollection
            builtinListUnit
            builtinListElement
            builtinListConcat
            (argument' . unparse2 <$> Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtinList
        InternalList { builtinListUnit } = builtinList
        InternalList { builtinListElement } = builtinList
        InternalList { builtinListConcat } = builtinList

-- * Builtin AC (associative-commutative) generic stuff

{- | Internal representation for associative-commutative domain values.
-}
data NormalizedAc key valueWrapper child = NormalizedAc
    { elementsWithVariables :: [(child, valueWrapper child)]
    -- ^ Non-concrete elements of the structure.
    -- These would be of sorts @(Int, String)@ for a map from @Int@ to @String@.
    , concreteElements :: Map key (valueWrapper child)
    -- ^ Concrete elements of the structure.
    -- These would be of sorts @(Int, String)@ for a map from @Int@ to @String@.
    , opaque :: [child]
    -- ^ Unoptimized (i.e. non-element) parts of the structure.
    }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Functor valueWrapper => Functor (NormalizedAc key valueWrapper) where
    fmap
        f
        NormalizedAc
            { elementsWithVariables
            , concreteElements
            , opaque
            }
      =
        NormalizedAc
            { elementsWithVariables = fmap pairF elementsWithVariables
            , concreteElements = fmap wrappedF concreteElements
            , opaque = fmap f opaque
            }
      where
        wrappedF a = fmap f a
        pairF (a, b) = (f a, fmap f b)

instance Foldable valueWrapper => Foldable (NormalizedAc key valueWrapper) where
    foldr
        :: forall child b
        . (child -> b -> b)
        -> b
        -> NormalizedAc key valueWrapper child
        -> b
    foldr
        f
        start
        ac@(NormalizedAc _ _ _)
      =
        foldr pairF
            (foldr wrappedF
                (foldr f start opaque)
                concreteElements
            )
            elementsWithVariables
      where
        NormalizedAc
            { elementsWithVariables
            , concreteElements
            , opaque
            }
          = ac

        wrappedF :: valueWrapper child -> b -> b
        wrappedF a merged = foldr f merged a

        pairF :: (child, valueWrapper child) -> b -> b
        pairF (a, b) merged = f a (foldr f merged b)

instance Traversable valueWrapper => Traversable (NormalizedAc key valueWrapper)
  where
    traverse
        :: forall child child' f
        .  Applicative f
        => (child -> f child')
        -> NormalizedAc key valueWrapper child
        -> f (NormalizedAc key valueWrapper child')
    traverse
        f
        NormalizedAc
            { elementsWithVariables
            , concreteElements
            , opaque
            }
      =
        NormalizedAc
        <$> traverse pairF elementsWithVariables
        <*> traverse wrappedF concreteElements
        <*> traverse f opaque
      where
        wrappedF :: valueWrapper child -> f (valueWrapper child')
        wrappedF a = traverse f a

        pairF :: (child, valueWrapper child) -> f (child', valueWrapper child')
        pairF (a, b) = (,) <$> f a <*> traverse f b

instance (Hashable key, Hashable (valueWrapper child), Hashable child)
    => Hashable (NormalizedAc key valueWrapper child)
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

instance (NFData key, NFData (valueWrapper child), NFData child)
    => NFData (NormalizedAc key valueWrapper child)

instance SOP.Generic (NormalizedAc key valueWrapper child)

instance SOP.HasDatatypeInfo (NormalizedAc key valueWrapper child)

instance (Debug key, Debug (valueWrapper child), Debug child)
    => Debug (NormalizedAc key valueWrapper child)

emptyNormalizedAc :: NormalizedAc key valueWrapper child
emptyNormalizedAc = NormalizedAc
    { elementsWithVariables = []
    , concreteElements = Map.empty
    , opaque = []
    }

{- | Internal representation of associative-commutative domain values.
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
class AcWrapper (normalized :: * -> * -> *) (valueWrapper :: * -> *)
    | normalized -> valueWrapper
    , valueWrapper -> normalized
  where
    unwrapAc :: normalized key child -> NormalizedAc key valueWrapper child
    wrapAc :: NormalizedAc key valueWrapper child -> normalized key child

    {-| Pairs the values in two wrappers as they should be paired for
    unification.
    -}
    acExactZip
        :: valueWrapper a -> valueWrapper b -> Maybe (valueWrapper (a, b))
    unparseElement
        :: (key -> Pretty.Doc ann)
        -> (child -> Pretty.Doc ann)
        -> (child, valueWrapper child) -> Pretty.Doc ann
    unparseConcreteElement
        :: (key -> Pretty.Doc ann)
        -> (child -> Pretty.Doc ann)
        -> (key, valueWrapper child) -> Pretty.Doc ann

unparsedChildren
    :: forall ann child key normalized valueWrapper
    .  (AcWrapper normalized valueWrapper)
    => (key -> Pretty.Doc ann)
    -> (child -> Pretty.Doc ann)
    -> normalized key child
    -> [Pretty.Doc ann]
unparsedChildren keyUnparser childUnparser wrapped =
    case unwrapped of
        -- case statement needed only for getting compiler notifications when
        -- the NormalizedAc field count changes
        NormalizedAc _ _ _ ->
            (elementUnparser <$> elementsWithVariables)
            ++ (concreteElementUnparser <$> Map.toAscList concreteElements)
            ++ (argument' . childUnparser <$> opaque)
  where
    unwrapped :: NormalizedAc key valueWrapper child
    unwrapped = unwrapAc wrapped

    NormalizedAc {elementsWithVariables} = unwrapped
    NormalizedAc {concreteElements} = unwrapped
    NormalizedAc {opaque} = unwrapped

    elementUnparser :: (child, valueWrapper child) -> Pretty.Doc ann
    elementUnparser = unparseElement keyUnparser childUnparser

    concreteElementUnparser :: (key, valueWrapper child) -> Pretty.Doc ann
    concreteElementUnparser =
        unparseConcreteElement keyUnparser childUnparser

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
    ( Unparse key
    , Unparse child
    , AcWrapper normalized value
    )
    => Unparse (InternalAc key normalized child)
  where
    unparse = unparseInternalAc unparse unparse
    unparse2 = unparseInternalAc unparse2 unparse2

unparseInternalAc
    :: (AcWrapper normalized value)
    => (key -> Pretty.Doc ann)
    -> (child -> Pretty.Doc ann)
    -> InternalAc key normalized child
    -> Pretty.Doc ann
unparseInternalAc keyUnparser childUnparser builtinAc =
    unparseCollection
        builtinAcUnit
        builtinAcElement
        builtinAcConcat
        (unparsedChildren keyUnparser childUnparser builtinAcChild)
  where
    InternalAc { builtinAcChild } = builtinAc
    InternalAc { builtinAcUnit } = builtinAc
    InternalAc { builtinAcElement } = builtinAc
    InternalAc { builtinAcConcat } = builtinAc

-- * Builtin Map

{- | Wrapper for map values.
-}
newtype Value child = Value {getValue :: child}
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance Hashable child => Hashable (Value child)
  where
    hashWithSalt salt (Value child) = hashWithSalt salt child

instance NFData child => NFData (Value child)

instance SOP.Generic (Value child)

instance SOP.HasDatatypeInfo (Value child)

instance Debug child => Debug (Value child)

instance Unparse a => Unparse (Value a) where
    unparse (Value a) = unparse a
    unparse2 (Value a) = unparse2 a

{- | Wrapper for normalized maps, to be used in the `builtinAcChild` field.
-}
newtype NormalizedMap key child =
    NormalizedMap {getNormalizedMap :: NormalizedAc key Value child}
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance (Hashable key, Hashable child) => Hashable (NormalizedMap key child)
  where
    hashWithSalt salt (NormalizedMap m) = hashWithSalt salt m

instance (NFData key, NFData child) => NFData (NormalizedMap key child)

instance SOP.Generic (NormalizedMap key child)

instance SOP.HasDatatypeInfo (NormalizedMap key child)

instance (Debug key, Debug child) => Debug (NormalizedMap key child)

instance AcWrapper NormalizedMap Value where
    wrapAc = NormalizedMap
    unwrapAc = getNormalizedMap
    acExactZip (Value a) (Value b) = Just (Value (a, b))
    unparseElement _keyUnparser childUnparser (key, Value value) =
        arguments' [childUnparser key, childUnparser value]
    unparseConcreteElement keyUnparser childUnparser (key, Value value) =
        arguments' [keyUnparser key, childUnparser value]

{- | Internal representation of the builtin @MAP.Map@ domain.
-}
type InternalMap key child = InternalAc key NormalizedMap child

-- * Builtin Set

{- | Wrapper for set values, i.e. a wrapper which does not allow any value
for a given key.
-}
data NoValue child = NoValue
    deriving (Eq, Foldable, Functor, Traversable, GHC.Generic, Ord, Show)

instance Unparse (NoValue a) where
    unparse _ = "<nothing>"
    unparse2 _ = "<nothing>"

instance Hashable (NoValue child)
  where
    hashWithSalt salt NoValue = hashWithSalt salt (0 :: Int)

instance NFData (NoValue child)

instance SOP.Generic (NoValue child)

instance SOP.HasDatatypeInfo (NoValue child)

instance Debug (NoValue child)

{- | Wrapper for normalized sets, to be used in the `builtinAcChild` field.
-}
newtype NormalizedSet key child =
    NormalizedSet {getNormalizedSet :: NormalizedAc key NoValue child}
    deriving (Eq, Foldable, Functor, Traversable, GHC.Generic, Ord, Show)

instance (Hashable key, Hashable child) => Hashable (NormalizedSet key child)
  where
    hashWithSalt salt (NormalizedSet set) =
        hashWithSalt salt set

instance (NFData key, NFData child) => NFData (NormalizedSet key child)

instance SOP.Generic (NormalizedSet key child)

instance SOP.HasDatatypeInfo (NormalizedSet key child)

instance (Debug key, Debug child) => Debug (NormalizedSet key child)

instance AcWrapper NormalizedSet NoValue where
    wrapAc = NormalizedSet
    unwrapAc = getNormalizedSet
    acExactZip _ _ = Just NoValue
    unparseElement _keyUnparser childUnparser (key, NoValue) =
        argument' (childUnparser key)
    unparseConcreteElement keyUnparser _childUnparser (key, NoValue) =
        argument' (keyUnparser key)

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

instance Synthetic (Builtin key) Sort where
    synthetic = builtinSort
    {-# INLINE synthetic #-}

makeLenses ''InternalList
makeLenses ''InternalAc
makeLenses ''InternalInt
makeLenses ''InternalBool
makeLenses ''InternalString

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
