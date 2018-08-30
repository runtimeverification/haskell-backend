{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Kore.Implicit.ImplicitSorts
Description : Haskell definitions for the implicit Kore 'Meta' sorts.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.ImplicitSorts where

import Kore.AST.Common
import Kore.Implicit.ImplicitSortsImpl

-- TODO(virgil-serbanuta): Add tests for "defined but not used" symbols
( charMetaSort, charListMetaSort
    , nilCharList, nilCharListA, consCharList, consCharListA
    , appendCharList, appendCharListA
    , inCharList, inCharListA
    , deleteCharList, deleteCharListA
    , charListAxioms
    )
  =
    defineMetaSort CharSort

( sortMetaSort, sortListMetaSort
    , nilSortList, nilSortListA, consSortList, consSortListA
    , appendSortList, appendSortListA
    , inSortList, inSortListA
    , deleteSortList, deleteSortListA
    , sortListAxioms
    )
  =
    defineMetaSort SortSort

( symbolMetaSort, symbolListMetaSort
    , nilSymbolList, nilSymbolListA, consSymbolList, consSymbolListA
    , appendSymbolList, appendSymbolListA
    , inSymbolList, inSymbolListA
    , deleteSymbolList, deleteSymbolListA
    , symbolListAxioms
    )
  =
    defineMetaSort SymbolSort

( variableMetaSort, variableListMetaSort
    , nilVariableList, nilVariableListA, consVariableList, consVariableListA
    , appendVariableList, appendVariableListA
    , inVariableList, inVariableListA
    , deleteVariableList, deleteVariableListA
    , variableListAxioms
    )
  =
    defineMetaSort VariableSort

( patternMetaSort, patternListMetaSort
    , nilPatternList, nilPatternListA, consPatternList, consPatternListA
    , appendPatternList, appendPatternListA
    , inPatternList, inPatternListA
    , deletePatternList, deletePatternListA
    , patternListAxioms
    )
  =
    defineMetaSort PatternSort

stringMetaSort = charListMetaSort
