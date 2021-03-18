{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE Strict #-}

module Kore.Builtin.Map.Map
    ( asTermLike
    -- * Symbols
    , lookupSymbolUpdate
    , lookupSymbolLookup
    , lookupSymbolInKeys
    , lookupSymbolKeys
    , lookupSymbolRemove
    , lookupSymbolRemoveAll
    , lookupSymbolSize
    , lookupSymbolValues
    , lookupSymbolInclusion
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
    , isSymbolRemove
    , isSymbolRemoveAll
    , isSymbolSize
    , isSymbolValues
    , isSymbolInclusion
    -- * Keys
    , concatKey
    , elementKey
    , in_keysKey
    , keysKey
    , keys_listKey
    , lookupKey
    , lookupOrDefaultKey
    , removeAllKey
    , removeKey
    , unitKey
    , updateKey
    , sizeKey
    , valuesKey
    , inclusionKey
    ) where

import Prelude.Kore

import qualified Data.Map.Strict as Map
import Data.String
    ( IsString
    )

import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.AssocComm.AssocComm as AssocComm
import qualified Kore.Builtin.Symbols as Builtin
import qualified Kore.Error as Kore
    ( Error
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.Internal.InternalMap
import Kore.Internal.TermLike as TermLike

concatKey :: IsString s => s
concatKey = "MAP.concat"

lookupKey :: IsString s => s
lookupKey = "MAP.lookup"

lookupOrDefaultKey :: IsString s => s
lookupOrDefaultKey = "MAP.lookupOrDefault"

elementKey :: IsString s => s
elementKey = "MAP.element"

unitKey :: IsString s => s
unitKey = "MAP.unit"

updateKey :: IsString s => s
updateKey = "MAP.update"

in_keysKey :: IsString s => s
in_keysKey = "MAP.in_keys"

keysKey :: IsString s => s
keysKey = "MAP.keys"

keys_listKey :: IsString s => s
keys_listKey = "MAP.keys_list"

removeKey :: IsString s => s
removeKey = "MAP.remove"

removeAllKey :: IsString s => s
removeAllKey = "MAP.removeAll"

sizeKey :: IsString s => s
sizeKey = "MAP.size"

valuesKey :: IsString s => s
valuesKey = "MAP.values"

inclusionKey :: IsString s => s
inclusionKey = "MAP.inclusion"

{- | Find the symbol hooked to @MAP.update@ in an indexed module.
 -}
lookupSymbolUpdate
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolUpdate = Builtin.lookupSymbol updateKey

{- | Find the symbol hooked to @MAP.lookup@ in an indexed module.
 -}
lookupSymbolLookup
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolLookup = Builtin.lookupSymbol lookupKey

{- | Find the symbol hooked to @MAP.in_keys@ in an indexed module.
 -}
lookupSymbolInKeys
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolInKeys = Builtin.lookupSymbol in_keysKey

{- | Find the symbol hooked to @MAP.keys@ in an indexed module.
 -}
lookupSymbolKeys
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolKeys = Builtin.lookupSymbol keysKey

{- | Find the symbol hooked to @MAP.remove@ in an indexed module.
 -}
lookupSymbolRemove
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolRemove = Builtin.lookupSymbol removeKey

{- | Find the symbol hooked to @MAP.removeAll@ in an indexed module.
 -}
lookupSymbolRemoveAll
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolRemoveAll = Builtin.lookupSymbol removeAllKey

{- | Find the symbol hooked to @MAP.size@ in an indexed module.
 -}
lookupSymbolSize
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolSize = Builtin.lookupSymbol sizeKey

{- | Find the symbol hooked to @MAP.values@ in an indexed module.
 -}
lookupSymbolValues
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolValues = Builtin.lookupSymbol valuesKey

{- | Find the symbol hooked to @MAP.inclusion@ in an indexed module.
 -}
lookupSymbolInclusion
    :: Sort
    -> VerifiedModule Attribute.Symbol
    -> Either (Kore.Error e) Symbol
lookupSymbolInclusion = Builtin.lookupSymbol inclusionKey

{- | Check if the given symbol is hooked to @MAP.concat@.
 -}
isSymbolConcat :: Symbol -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

{- | Check if the given symbol is hooked to @MAP.element@.
 -}
isSymbolElement :: Symbol -> Bool
isSymbolElement = Builtin.isSymbol elementKey

{- | Check if the given symbol is hooked to @MAP.unit@.
-}
isSymbolUnit :: Symbol -> Bool
isSymbolUnit = Builtin.isSymbol unitKey

{- | Check if the given symbol is hooked to @MAP.remove@.
-}
isSymbolRemove :: Symbol -> Bool
isSymbolRemove = Builtin.isSymbol removeKey

{- | Check if the given symbol is hooked to @MAP.removeAll@.
-}
isSymbolRemoveAll :: Symbol -> Bool
isSymbolRemoveAll = Builtin.isSymbol removeAllKey

{- | Check if the given symbol is hooked to @MAP.size@.
-}
isSymbolSize :: Symbol -> Bool
isSymbolSize = Builtin.isSymbol sizeKey

{- | Check if the given symbol is hooked to @MAP.values@.
-}
isSymbolValues :: Symbol -> Bool
isSymbolValues = Builtin.isSymbol valuesKey

{- | Check if the given symbol is hooked to @MAP.inclusion@.
-}
isSymbolInclusion :: Symbol -> Bool
isSymbolInclusion = Builtin.isSymbol inclusionKey

{- | Externalizes a 'Domain.InternalMap' as a 'TermLike'.
 -}
asTermLike
    :: forall variable
    .  InternalVariable variable
    => InternalMap Key (TermLike variable)
    -> TermLike variable
asTermLike builtin =
    AssocComm.asTermLike
        (AssocComm.UnitSymbol unitSymbol)
        (AssocComm.ConcatSymbol concatSymbol)
        (AssocComm.ConcreteElements
            (map concreteElement (Map.toAscList concreteElements))
        )
        (AssocComm.VariableElements
            (element . unwrapElement <$> elementsWithVariables)
        )
        (AssocComm.Opaque filteredMaps)
  where
    filteredMaps :: [TermLike variable]
    filteredMaps = filter (not . isEmptyMap) opaque

    isEmptyMap :: TermLike variable -> Bool
    isEmptyMap (InternalMap_ InternalAc { builtinAcChild = wrappedChild }) =
        unwrapAc wrappedChild == emptyNormalizedAc
    isEmptyMap (App_ symbol _) = unitSymbol == symbol
    isEmptyMap _ = False

    InternalAc { builtinAcChild } = builtin
    InternalAc { builtinAcUnit = unitSymbol } = builtin
    InternalAc { builtinAcElement = elementSymbol } = builtin
    InternalAc { builtinAcConcat = concatSymbol } = builtin

    normalizedAc = unwrapAc builtinAcChild

    NormalizedAc { elementsWithVariables } = normalizedAc
    NormalizedAc { concreteElements } = normalizedAc
    NormalizedAc { opaque } = normalizedAc

    concreteElement
        :: (Key, MapValue (TermLike variable))
        -> TermLike variable
    concreteElement (key, value) = element (into @(TermLike variable) key, value)

    element
        :: (TermLike variable, MapValue (TermLike variable))
        -> TermLike variable
    element (key, MapValue value) =
        mkApplySymbol elementSymbol [key, value]
