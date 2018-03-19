{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Data.Kore.Implicit.ImplicitSorts where

import           Data.Kore.AST.Common
import           Data.Kore.Implicit.ImplicitSortsImpl

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
