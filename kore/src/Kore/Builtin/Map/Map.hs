{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

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
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
    , isSymbolRemove
    , isSymbolRemoveAll
    , isSymbolSize
    -- * Keys
    , concatKey
    , elementKey
    , in_keysKey
    , keysKey
    , lookupKey
    , removeAllKey
    , removeKey
    , unitKey
    , updateKey
    , sizeKey
    ) where

import qualified Data.Map as Map
import Data.String
    ( IsString
    )

import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.AssocComm.AssocComm as AssocComm
import qualified Kore.Builtin.Symbols as Builtin
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error as Kore
    ( Error
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.Internal.TermLike as TermLike
import Kore.Sort
    ( Sort
    )

concatKey :: IsString s => s
concatKey = "MAP.concat"

lookupKey :: IsString s => s
lookupKey = "MAP.lookup"

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

removeKey :: IsString s => s
removeKey = "MAP.remove"

removeAllKey :: IsString s => s
removeAllKey = "MAP.removeAll"

sizeKey :: IsString s => s
sizeKey = "MAP.size"

{- | Find the symbol hooked to @MAP.update@ in an indexed module.
 -}
lookupSymbolUpdate
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolUpdate = Builtin.lookupSymbol updateKey

{- | Find the symbol hooked to @MAP.lookup@ in an indexed module.
 -}
lookupSymbolLookup
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolLookup = Builtin.lookupSymbol lookupKey

{- | Find the symbol hooked to @MAP.in_keys@ in an indexed module.
 -}
lookupSymbolInKeys
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolInKeys = Builtin.lookupSymbol in_keysKey

{- | Find the symbol hooked to @MAP.keys@ in an indexed module.
 -}
lookupSymbolKeys
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolKeys = Builtin.lookupSymbol keysKey

{- | Find the symbol hooked to @MAP.remove@ in an indexed module.
 -}
lookupSymbolRemove
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolRemove = Builtin.lookupSymbol removeKey

{- | Find the symbol hooked to @MAP.removeAll@ in an indexed module.
 -}
lookupSymbolRemoveAll
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolRemoveAll = Builtin.lookupSymbol removeAllKey

{- | Find the symbol hooked to @MAP.size@ in an indexed module.
 -}
lookupSymbolSize
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolSize = Builtin.lookupSymbol sizeKey

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

{- | Externalizes a 'Domain.InternalMap' as a 'TermLike'.
 -}
asTermLike
    :: forall variable
    .  InternalVariable variable
    => Domain.InternalMap (TermLike Concrete) (TermLike variable)
    -> TermLike variable
asTermLike builtin =
    AssocComm.asTermLike
        (AssocComm.UnitSymbol unitSymbol)
        (AssocComm.ConcatSymbol concatSymbol)
        (AssocComm.ConcreteElements
            (map concreteElement (Map.toAscList concreteElements))
        )
        (AssocComm.VariableElements
            (element . Domain.unwrapElement <$> elementsWithVariables)
        )
        (AssocComm.Opaque filteredMaps)
  where
    filteredMaps :: [TermLike variable]
    filteredMaps = filter (not . isEmptyMap) opaque

    isEmptyMap :: TermLike variable -> Bool
    isEmptyMap
        (Builtin_
            (Domain.BuiltinMap
                Domain.InternalAc { builtinAcChild = wrappedChild }
            )
        )
      =
        Domain.unwrapAc wrappedChild == Domain.emptyNormalizedAc
    isEmptyMap (App_ symbol _) = unitSymbol == symbol
    isEmptyMap _ = False

    Domain.InternalAc { builtinAcChild } = builtin
    Domain.InternalAc { builtinAcUnit = unitSymbol } = builtin
    Domain.InternalAc { builtinAcElement = elementSymbol } = builtin
    Domain.InternalAc { builtinAcConcat = concatSymbol } = builtin

    normalizedAc = Domain.unwrapAc builtinAcChild

    Domain.NormalizedAc { elementsWithVariables } = normalizedAc
    Domain.NormalizedAc { concreteElements } = normalizedAc
    Domain.NormalizedAc { opaque } = normalizedAc

    concreteElement
        :: (TermLike Concrete, Domain.MapValue (TermLike variable))
        -> TermLike variable
    concreteElement (key, value) = element (TermLike.fromConcrete key, value)
    element
        :: (TermLike variable, Domain.MapValue (TermLike variable))
        -> TermLike variable
    element (key, Domain.MapValue value) =
        mkApplySymbol elementSymbol [key, value]
