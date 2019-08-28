{- |
Module      : Kore.Builtin.SetSymbols
Description : Tools for handling the symbols involved with map biltins
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.SetSymbols as Set
@
-}

module Kore.Builtin.SetSymbols
    ( -- * Symbols
      isSymbolConcat
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

import           Data.String
                 ( IsString )
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Error as Kore
                 ( Error )
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Internal.Symbol
                 ( Symbol )
import           Kore.Sort
                 ( Sort )

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
