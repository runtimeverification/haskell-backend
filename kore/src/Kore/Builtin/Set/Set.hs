{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Builtin.Set.Set
    ( asTermLike
    -- * Symbols
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
    , isSymbolList2set
    , lookupSymbolIn
    , lookupSymbolDifference
    , lookupSymbolList2set
      -- * Keys
    , concatKey
    , differenceKey
    , elementKey
    , inKey
    , intersectionKey
    , sizeKey
    , toListKey
    , unitKey
    , list2setKey
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

{- | Find the symbol hooked to @SET.get@ in an indexed module.
 -}
lookupSymbolIn
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolIn = Builtin.lookupSymbol inKey

{- | Find the symbol hooked to @SET.difference@ in an indexed module.
 -}
lookupSymbolDifference
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolDifference = Builtin.lookupSymbol differenceKey

{- | Find the symbol hooked to @SET.list2set@ in an indexed module.
 -}
lookupSymbolList2set
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolList2set = Builtin.lookupSymbol list2setKey

{- | Check if the given symbol is hooked to @SET.concat@.
 -}
isSymbolConcat :: Symbol -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

{- | Check if the given symbol is hooked to @SET.element@.
 -}
isSymbolElement :: Symbol -> Bool
isSymbolElement = Builtin.isSymbol elementKey

{- | Check if the given symbol is hooked to @SET.unit@.
-}
isSymbolUnit :: Symbol -> Bool
isSymbolUnit = Builtin.isSymbol unitKey

{- | Check if the given symbol is hooked to @SET.set2list@.
-}
isSymbolList2set :: Symbol -> Bool
isSymbolList2set = Builtin.isSymbol list2setKey

{- | Externalizes a 'Domain.InternalSet' as a 'TermLike'.
-}
asTermLike
    :: forall variable
    .  InternalVariable variable
    => Domain.InternalSet (TermLike Concrete) (TermLike variable)
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
        (AssocComm.Opaque filteredSets)
  where
    filteredSets :: [TermLike variable]
    filteredSets = filter (not . isEmptySet) opaque

    isEmptySet :: TermLike variable -> Bool
    isEmptySet
        (Builtin_
            (Domain.BuiltinSet
                Domain.InternalAc { builtinAcChild = wrappedChild }
            )
        )
      =
        Domain.unwrapAc wrappedChild == Domain.emptyNormalizedAc
    isEmptySet (App_ symbol _) = unitSymbol == symbol
    isEmptySet _ = False

    Domain.InternalAc { builtinAcChild } = builtin
    Domain.InternalAc { builtinAcUnit = unitSymbol } = builtin
    Domain.InternalAc { builtinAcElement = elementSymbol } = builtin
    Domain.InternalAc { builtinAcConcat = concatSymbol } = builtin

    normalizedAc = Domain.unwrapAc builtinAcChild

    Domain.NormalizedAc { elementsWithVariables } = normalizedAc
    Domain.NormalizedAc { concreteElements } = normalizedAc
    Domain.NormalizedAc { opaque } = normalizedAc

    concreteElement
        :: (TermLike Concrete, Domain.SetValue (TermLike variable))
        -> TermLike variable
    concreteElement (key, value) = element (TermLike.fromConcrete key, value)
    element
        :: (TermLike variable, Domain.SetValue (TermLike variable))
        -> TermLike variable
    element (key, Domain.SetValue) = mkApplySymbol elementSymbol [key]
