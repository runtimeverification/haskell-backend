{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

{-# LANGUAGE Strict #-}

module Kore.Internal.NormalizedAc
    ( AcWrapper (..)
    , wrapElement, unwrapElement
    , wrapConcreteElement
    , NormalizedAc (..)
    , nullAc
    , emptyNormalizedAc
    , emptyInternalAc
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
    , unparsedChildren
    , InternalAc (..)
    , normalizedAcDefined
    , normalizedAcConstructorLike
    , normalizedAcFunctional
    , unparseInternalAc
    , PairWiseElements (..)
    , generatePairWiseElements
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Control.Lens.Iso
    ( Iso'
    )
import Data.Default
import Data.Kind
    ( Type
    )
import Data.List.Extra
    ( nubOrdBy
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Concat as Att
import qualified Kore.Attribute.Element as Att
import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.Functional
import qualified Kore.Attribute.Symbol as SymAtt
import qualified Kore.Attribute.Unit as Att
import Kore.Debug
import Kore.Internal.Symbol hiding
    ( isConstructorLike
    )
import Kore.Sort
import Kore.Unparser
import Pretty
    ( (<+>)
    )
import qualified Pretty

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
    :: forall ann child normalized key
    .  AcWrapper normalized
    => Att.Element (Pretty.Doc ann)
    -> (key -> Pretty.Doc ann)
    -> (child -> Pretty.Doc ann)
    -> normalized key child
    -> [Pretty.Doc ann]
unparsedChildren elementSymbol keyUnparser childUnparser wrapped
  | Just elementSymbolDoc <- Att.getElement elementSymbol =
    (elementUnparser elementSymbolDoc <$> elementsWithVariables)
    ++ (concreteElementUnparser elementSymbolDoc
        <$> Map.toAscList concreteElements)
    ++ (child . childUnparser <$> opaque)
  | isNothing (Att.getElement elementSymbol)
  , null elementsWithVariables
  , null concreteElements =
    child . childUnparser <$> opaque
  | otherwise = error "Cannot unparse nonempty element lists without an Element symbol"
  where
    unwrapped :: NormalizedAc normalized key child
    -- Matching needed only for getting compiler notifications when
    -- the NormalizedAc field count changes.
    unwrapped@(NormalizedAc _ _ _) = unwrapAc wrapped

    NormalizedAc {elementsWithVariables} = unwrapped
    NormalizedAc {concreteElements} = unwrapped
    NormalizedAc {opaque} = unwrapped
    element = (<>) . (<+>) "/* element: */"
    concreteElement = (<>) . (<+>) "/* concrete element: */"
    child = (<+>) "/* opaque child: */"

    elementUnparser :: Pretty.Doc ann -> Element normalized child -> Pretty.Doc ann
    elementUnparser elementSymbolDoc =
        element elementSymbolDoc
        . unparseElement childUnparser

    concreteElementUnparser :: Pretty.Doc ann -> (key, Value normalized child) -> Pretty.Doc ann
    concreteElementUnparser elementSymbolDoc =
        concreteElement elementSymbolDoc
        . unparseConcreteElement keyUnparser childUnparser

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

emptyNormalizedAc :: NormalizedAc valueWrapper key child
emptyNormalizedAc = NormalizedAc
    { elementsWithVariables = []
    , concreteElements = Map.empty
    , opaque = []
    }

asSingleOpaqueElem
    :: NormalizedAc valueWrapper key child
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
data InternalAc (normalized :: Type -> Type -> Type) key child =
    InternalAc
        { builtinAcSort :: !Sort
        , builtinAcUnit :: !(Att.Unit Symbol)
        , builtinAcElement :: !(Att.Element Symbol)
        , builtinAcConcat :: !(Att.Concat Symbol)
        , builtinAcChild :: normalized key child
        }
    deriving (Show)
    deriving (Foldable, Functor, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Eq (normalized key child)
    => Eq (InternalAc normalized key child) where
    internal1 == internal2 =
        builtinAcSort internal1 == builtinAcSort internal2
        && builtinAcChild internal1 == builtinAcChild internal2

instance Ord (normalized key child)
    => Ord (InternalAc normalized key child) where
    internal1 <= internal2 =
        if builtinAcSort internal1 == builtinAcSort internal2
            then builtinAcChild internal1 <= builtinAcChild internal2
            else builtinAcSort internal1 <= builtinAcSort internal2

instance Hashable (normalized key child)
    => Hashable (InternalAc normalized key child)
  where
    hashWithSalt salt builtin =
        hashWithSalt (hashWithSalt salt builtinAcSort) builtinAcChild
      where
        InternalAc { builtinAcSort } = builtin
        InternalAc { builtinAcChild } = builtin

instance (NFData (normalized key child))
    => NFData (InternalAc normalized key child)

instance (Debug (normalized key child))
    => Debug (InternalAc normalized key child)

instance
    (Debug (normalized key child), Diff (normalized key child))
    => Diff (InternalAc normalized key child)

emptyInternalAc
    :: (AcWrapper normalized)
    => Sort
    -> InternalAc normalized key child
emptyInternalAc sort = InternalAc
    { builtinAcSort = sort
    , builtinAcUnit = def
    , builtinAcElement = def
    , builtinAcConcat = def
    , builtinAcChild = wrapAc emptyNormalizedAc
    }

unparseInternalAc
    :: (AcWrapper normalized)
    => HasCallStack
    => (key -> Pretty.Doc ann)
    -> (child -> Pretty.Doc ann)
    -> InternalAc normalized key child
    -> Pretty.Doc ann
unparseInternalAc keyUnparser childUnparser builtinAc =
    unparseConcat'
        (Att.fromUnit $ unparse <$> unitSymbolOrAlias)
        (Att.fromConcat $ unparse <$> builtinAcConcat)
        children
  where
    InternalAc { builtinAcChild } = builtinAc
    InternalAc { builtinAcUnit } = builtinAc
    InternalAc { builtinAcElement } = builtinAc
    InternalAc { builtinAcConcat } = builtinAc
    (concatUnit, concatElement) = case Att.getConcat builtinAcConcat of
        Nothing -> (def, def)
        Just concatSymbol -> let concatAtts = symbolAttributes concatSymbol in
            ( SymAtt.unitSymbol concatAtts
            , SymAtt.elementSymbol concatAtts
            )
    unitSymbolOrAlias = Att.mergeUnit
        (toSymbolOrAlias <$> builtinAcUnit)
        concatUnit
    elementSymbolOrAlias = Att.mergeElement
        (toSymbolOrAlias <$> builtinAcElement)
        concatElement
    children = unparsedChildren
        (unparse <$> elementSymbolOrAlias)
        keyUnparser
        childUnparser
        builtinAcChild


normalizedAcDefined
    :: (Foldable (Element collection), Foldable (Value collection))
    => NormalizedAc collection key Defined -> Defined
normalizedAcDefined ac@(NormalizedAc _ _ _) =
    case ac of
        NormalizedAc
            { elementsWithVariables = []
            , opaque = []
            } -> sameAsChildren
        NormalizedAc
            { elementsWithVariables = [_]
            , concreteElements
            , opaque = []
            }
          | Map.null concreteElements -> sameAsChildren
        NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = [_]
            }
          | Map.null concreteElements -> sameAsChildren
        _ -> Defined False
  where
    sameAsChildren = fold ac

normalizedAcFunctional
    :: (Foldable (Element collection), Foldable (Value collection))
    => NormalizedAc collection key Functional -> Functional
normalizedAcFunctional ac@(NormalizedAc _ _ _) =
    case ac of
        NormalizedAc
            { elementsWithVariables = []
            , opaque = []
            } -> sameAsChildren
        NormalizedAc
            { elementsWithVariables = [_]
            , concreteElements
            , opaque = []
            }
          | Map.null concreteElements -> sameAsChildren
        NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = [_]
            }
          | Map.null concreteElements -> sameAsChildren
        _ -> Functional False
  where
    sameAsChildren = fold ac

normalizedAcConstructorLike
    ::  ( HasConstructorLike key
        , HasConstructorLike (Value collection ConstructorLike)
        )
    => NormalizedAc collection key ConstructorLike -> ConstructorLike
normalizedAcConstructorLike ac@(NormalizedAc _ _ _) =
    case ac of
        NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = []
            }
              | all pairIsConstructorLike concreteElementsList
                -> ConstructorLike . Just $ ConstructorLikeHead
              where
                concreteElementsList = Map.toList concreteElements
                pairIsConstructorLike (key, value) =
                    assertConstructorLike "" key $ isConstructorLike value
        _ -> ConstructorLike Nothing

-- | 'PairWiseElements' is a representation of the elements of all subcollections
-- necessary for proving the definedness of a collection.
data PairWiseElements normalized key child =
    PairWiseElements
        { symbolicPairs
            :: [(Element normalized child, Element normalized child)]
        , concretePairs
            :: [((key, Value normalized child), (key, Value normalized child))]
        , opaquePairs
            :: [(child, child)]
        , symbolicConcretePairs
            :: [(Element normalized child, (key, Value normalized child))]
        , symbolicOpaquePairs
            :: [(Element normalized child, child)]
        , concreteOpaquePairs
            :: [((key, Value normalized child), child)]
        }

-- | Generates the 'PairWiseElements' for a 'AcWrapper' collection.
generatePairWiseElements
    :: AcWrapper normalized
    => Ord key
    => Ord child
    => Ord (Element normalized child)
    => Ord (Value normalized child)
    => normalized key child
    -> PairWiseElements normalized key child
generatePairWiseElements (unwrapAc -> normalized) =
    PairWiseElements
        { symbolicPairs = pairWiseElemsOfSameType symbolicElems
        , concretePairs = pairWiseElemsOfSameType concreteElems
        , opaquePairs   = pairWiseElemsOfSameType opaqueElems
        , symbolicConcretePairs =
            (,) <$> symbolicElems <*> concreteElems
        , symbolicOpaquePairs =
            (,) <$> symbolicElems <*> opaqueElems
        , concreteOpaquePairs =
            (,) <$> concreteElems <*> opaqueElems
        }
  where
    symbolicElems = elementsWithVariables normalized
    concreteElems = Map.toList . concreteElements $ normalized
    opaqueElems = opaque normalized
    pairWiseElemsOfSameType elems =
        [ (x, y) | x <- elems, y <- elems, x /= y ]
        & nubOrdBy applyComm
    applyComm p1 p2
      | p1 == p2 = EQ
      | swap p1 == p2 = EQ
      | otherwise = compare p1 p2
