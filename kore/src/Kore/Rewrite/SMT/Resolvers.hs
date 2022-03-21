{- |
Module      : Kore.Rewrite.SMT.Resolvers
Description : Translates sorts and symbols to a SMT representation.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Rewrite.SMT.Resolvers (
    translateSort,
    translateSymbol,
) where

import Data.Map.Strict qualified as Map
import Data.Reflection (
    Given,
    given,
 )
import Kore.Attribute.Symbol qualified as Attribute
import Kore.IndexedModule.MetadataTools (
    MetadataTools,
    SmtMetadataTools,
 )
import Kore.Internal.Symbol
import Kore.Rewrite.SMT.AST qualified as AST (
    Declarations (Declarations),
    Sort (Sort),
    Symbol (Symbol),
    symbolSmtFromSortArgs,
 )
import Kore.Rewrite.SMT.Representation.Sorts qualified as AST (
    sortSmtFromSortArgs,
 )
import Kore.Rewrite.SMT.AST qualified as AST.DoNotUse
import Kore.Sort (
    Sort (SortActualSort, SortVariableSort),
    SortActual (SortActual, sortActualName, sortActualSorts),
 )
import Prelude.Kore
import SMT qualified

{- | Creates the SMT representation of a symbol assuming the smt declarations in
the given SmtMetadataTools.
-}
translateSymbol ::
    MetadataTools metadata
    Given (SmtMetadataTools metadata Attribute.Symbol) =>
    Symbol ->
    Maybe SMT.SExpr
translateSymbol Symbol{symbolConstructor, symbolParams} = do
    AST.Symbol{symbolData} <- Map.lookup symbolConstructor symbols
    AST.symbolSmtFromSortArgs symbolData sorts symbolParams
  where
    AST.Declarations{sorts, symbols} = smtData tools

    tools :: SmtMetadataTools Attribute.Symbol
    tools = given

translateSort ::
    Given (SmtMetadataTools Attribute.Symbol) =>
    Sort ->
    Maybe SMT.SExpr
translateSort
    (SortActualSort SortActual{sortActualName, sortActualSorts}) =
        do
            AST.Sort{sortData} <- Map.lookup sortActualName sorts
            AST.sortSmtFromSortArgs sortData sorts sortActualSorts
      where
        MetadataTools{smtData = AST.Declarations{sorts}} = tools

        tools :: SmtMetadataTools Attribute.Symbol
        tools = given
translateSort (SortVariableSort _) = Nothing
