{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Builtin.Set.Set (
    asTermLike,

    -- * Symbols
    isSymbolConcat,
    isSymbolElement,
    isSymbolUnit,
    isSymbolList2set,
    isSymbolInclusion,
    lookupSymbolIn,
    lookupSymbolDifference,
    lookupSymbolList2set,
    lookupSymbolInclusion,

    -- * Keys
    concatKey,
    differenceKey,
    elementKey,
    inKey,
    intersectionKey,
    sizeKey,
    toListKey,
    unitKey,
    list2setKey,
    inclusionKey,
) where

import Prelude.Kore

import qualified Data.Map.Strict as Map
import Data.String (
    IsString,
 )

import Kore.Attribute.Element hiding (
    elementSymbol,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin.AssocComm.AssocComm as AssocComm
import qualified Kore.Builtin.Symbols as Builtin
import qualified Kore.Error as Kore (
    Error,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.InternalSet
import Kore.Internal.TermLike as TermLike

concatKey :: IsString s => s
concatKey = "SET.concat"

elementKey :: IsString s => s
elementKey = "SET.element"

unitKey :: IsString s => s
unitKey = "SET.unit"

inKey :: IsString s => s
inKey = "SET.in"

differenceKey :: IsString s => s
differenceKey = "SET.difference"

toListKey :: IsString s => s
toListKey = "SET.set2list"

sizeKey :: IsString s => s
sizeKey = "SET.size"

intersectionKey :: IsString s => s
intersectionKey = "SET.intersection"

list2setKey :: IsString s => s
list2setKey = "SET.list2set"

inclusionKey :: IsString s => s
inclusionKey = "SET.inclusion"

-- | Find the symbol hooked to @SET.get@ in an indexed module.
lookupSymbolIn ::
    Sort ->
    VerifiedModule Attribute.Symbol ->
    Either (Kore.Error e) Symbol
lookupSymbolIn = Builtin.lookupSymbol inKey

-- | Find the symbol hooked to @SET.difference@ in an indexed module.
lookupSymbolDifference ::
    Sort ->
    VerifiedModule Attribute.Symbol ->
    Either (Kore.Error e) Symbol
lookupSymbolDifference = Builtin.lookupSymbol differenceKey

-- | Find the symbol hooked to @SET.list2set@ in an indexed module.
lookupSymbolList2set ::
    Sort ->
    VerifiedModule Attribute.Symbol ->
    Either (Kore.Error e) Symbol
lookupSymbolList2set = Builtin.lookupSymbol list2setKey

-- | Find the symbol hooked to @SET.inclusion@ in an indexed module.
lookupSymbolInclusion ::
    Sort ->
    VerifiedModule Attribute.Symbol ->
    Either (Kore.Error e) Symbol
lookupSymbolInclusion = Builtin.lookupSymbol inclusionKey

-- | Check if the given symbol is hooked to @SET.concat@.
isSymbolConcat :: Symbol -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

-- | Check if the given symbol is hooked to @SET.element@.
isSymbolElement :: Symbol -> Bool
isSymbolElement = Builtin.isSymbol elementKey

-- | Check if the given symbol is hooked to @SET.unit@.
isSymbolUnit :: Symbol -> Bool
isSymbolUnit = Builtin.isSymbol unitKey

-- | Check if the given symbol is hooked to @SET.set2list@.
isSymbolList2set :: Symbol -> Bool
isSymbolList2set = Builtin.isSymbol list2setKey

-- | Check if the given symbol is hooked to @SET.inclusion@.
isSymbolInclusion :: Symbol -> Bool
isSymbolInclusion = Builtin.isSymbol inclusionKey

-- TODO (thomas.tuegel): Rename this function.

-- | Externalizes a 'Domain.InternalSet' as a 'TermLike'.
asTermLike ::
    forall variable.
    InternalVariable variable =>
    HasCallStack =>
    InternalSet Key (TermLike variable) ->
    TermLike variable
asTermLike builtin =
    AssocComm.asTermLike
        unitSymbol
        concatSymbol
        ( AssocComm.ConcreteElements
            (map concreteElement (Map.toAscList concreteElements))
        )
        ( AssocComm.VariableElements
            (element . unwrapElement <$> elementsWithVariables)
        )
        (AssocComm.Opaque filteredSets)
  where
    filteredSets :: [TermLike variable]
    filteredSets = filter (not . isEmptySet) opaque

    isEmptySet :: TermLike variable -> Bool
    isEmptySet (InternalSet_ InternalAc{builtinAcChild = wrappedChild}) =
        unwrapAc wrappedChild == emptyNormalizedAc
    isEmptySet (App_ symbol _) = isSymbolUnit symbol
    isEmptySet _ = False

    InternalAc{builtinAcChild} = builtin
    InternalAc{builtinAcUnit = unitSymbol} = builtin
    InternalAc{builtinAcElement = elementSymbol} = builtin
    InternalAc{builtinAcConcat = concatSymbol} = builtin

    normalizedAc = unwrapAc builtinAcChild

    NormalizedAc{elementsWithVariables} = normalizedAc
    NormalizedAc{concreteElements} = normalizedAc
    NormalizedAc{opaque} = normalizedAc

    concreteElement ::
        (Key, SetValue (TermLike variable)) ->
        TermLike variable
    concreteElement (key, value) = element (from @Key key, value)

    element ::
        HasCallStack =>
        (TermLike variable, SetValue (TermLike variable)) ->
        TermLike variable
    element (key, SetValue) =
        mkApplySymbol (fromElement elementSymbol) [key]
