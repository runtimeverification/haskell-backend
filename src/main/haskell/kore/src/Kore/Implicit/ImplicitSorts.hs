{-|
Module      : Kore.Implicit.ImplicitSorts
Description : Haskell definitions for the implicit Kore 'Meta' sorts.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.ImplicitSorts where

import Kore.AST.MetaOrObject
import Kore.Implicit.ImplicitSortsImpl
import Kore.MetaML.AST
import Kore.Sort

-- TODO(virgil-serbanuta): Add tests for "defined but not used" symbols
charMetaSort     :: Sort Meta
charListMetaSort :: Sort Meta
nilCharList      :: MetaSentenceSymbol
nilCharListA     :: MetaPatternStub
consCharList     :: MetaSentenceSymbol
consCharListA    :: [MetaPatternStub] -> MetaPatternStub
appendCharList   :: MetaSentenceSymbol
appendCharListA  :: [MetaPatternStub] -> MetaPatternStub
inCharList       :: MetaSentenceSymbol
inCharListA      :: [Sort Meta] -> [MetaPatternStub] -> MetaPatternStub
deleteCharList   :: MetaSentenceSymbol
deleteCharListA  :: [MetaPatternStub] -> MetaPatternStub
charListAxioms   :: [MetaSentenceAxiom]
( charMetaSort, charListMetaSort
    , nilCharList, nilCharListA, consCharList, consCharListA
    , appendCharList, appendCharListA
    , inCharList, inCharListA
    , deleteCharList, deleteCharListA
    , charListAxioms
    )
  =
    defineMetaSort CharSort

sortMetaSort     :: Sort Meta
sortListMetaSort :: Sort Meta
nilSortList      :: MetaSentenceSymbol
nilSortListA     :: MetaPatternStub
consSortList     :: MetaSentenceSymbol
consSortListA    :: [MetaPatternStub] -> MetaPatternStub
appendSortList   :: MetaSentenceSymbol
appendSortListA  :: [MetaPatternStub] -> MetaPatternStub
inSortList       :: MetaSentenceSymbol
inSortListA      :: [Sort Meta] -> [MetaPatternStub] -> MetaPatternStub
deleteSortList   :: MetaSentenceSymbol
deleteSortListA  :: [MetaPatternStub] -> MetaPatternStub
sortListAxioms   :: [MetaSentenceAxiom]
( sortMetaSort, sortListMetaSort
    , nilSortList, nilSortListA, consSortList, consSortListA
    , appendSortList, appendSortListA
    , inSortList, inSortListA
    , deleteSortList, deleteSortListA
    , sortListAxioms
    )
  =
    defineMetaSort SortSort

symbolMetaSort     :: Sort Meta
symbolListMetaSort :: Sort Meta
nilSymbolList      :: MetaSentenceSymbol
nilSymbolListA     :: MetaPatternStub
consSymbolList     :: MetaSentenceSymbol
consSymbolListA    :: [MetaPatternStub] -> MetaPatternStub
appendSymbolList   :: MetaSentenceSymbol
appendSymbolListA  :: [MetaPatternStub] -> MetaPatternStub
inSymbolList       :: MetaSentenceSymbol
inSymbolListA      :: [Sort Meta] -> [MetaPatternStub] -> MetaPatternStub
deleteSymbolList   :: MetaSentenceSymbol
deleteSymbolListA  :: [MetaPatternStub] -> MetaPatternStub
symbolListAxioms   :: [MetaSentenceAxiom]
( symbolMetaSort, symbolListMetaSort
    , nilSymbolList, nilSymbolListA, consSymbolList, consSymbolListA
    , appendSymbolList, appendSymbolListA
    , inSymbolList, inSymbolListA
    , deleteSymbolList, deleteSymbolListA
    , symbolListAxioms
    )
  =
    defineMetaSort SymbolSort

variableMetaSort     :: Sort Meta
variableListMetaSort :: Sort Meta
nilVariableList      :: MetaSentenceSymbol
nilVariableListA     :: MetaPatternStub
consVariableList     :: MetaSentenceSymbol
consVariableListA    :: [MetaPatternStub] -> MetaPatternStub
appendVariableList   :: MetaSentenceSymbol
appendVariableListA  :: [MetaPatternStub] -> MetaPatternStub
inVariableList       :: MetaSentenceSymbol
inVariableListA      :: [Sort Meta] -> [MetaPatternStub] -> MetaPatternStub
deleteVariableList   :: MetaSentenceSymbol
deleteVariableListA  :: [MetaPatternStub] -> MetaPatternStub
variableListAxioms   :: [MetaSentenceAxiom]
( variableMetaSort, variableListMetaSort
    , nilVariableList, nilVariableListA, consVariableList, consVariableListA
    , appendVariableList, appendVariableListA
    , inVariableList, inVariableListA
    , deleteVariableList, deleteVariableListA
    , variableListAxioms
    )
  =
    defineMetaSort VariableSort

patternMetaSort     :: Sort Meta
patternListMetaSort :: Sort Meta
nilPatternList      :: MetaSentenceSymbol
nilPatternListA     :: MetaPatternStub
consPatternList     :: MetaSentenceSymbol
consPatternListA    :: [MetaPatternStub] -> MetaPatternStub
appendPatternList   :: MetaSentenceSymbol
appendPatternListA  :: [MetaPatternStub] -> MetaPatternStub
inPatternList       :: MetaSentenceSymbol
inPatternListA      :: [Sort Meta] -> [MetaPatternStub] -> MetaPatternStub
deletePatternList   :: MetaSentenceSymbol
deletePatternListA  :: [MetaPatternStub] -> MetaPatternStub
patternListAxioms   :: [MetaSentenceAxiom]
( patternMetaSort, patternListMetaSort
    , nilPatternList, nilPatternListA, consPatternList, consPatternListA
    , appendPatternList, appendPatternListA
    , inPatternList, inPatternListA
    , deletePatternList, deletePatternListA
    , patternListAxioms
    )
  =
    defineMetaSort PatternSort

stringMetaSort :: Sort Meta
stringMetaSort = charListMetaSort
