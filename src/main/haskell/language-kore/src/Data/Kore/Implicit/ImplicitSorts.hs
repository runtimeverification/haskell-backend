{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.Implicit.ImplicitSorts
Description : Haskell definitions for the implicit Kore 'Meta' sorts.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

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

getPatternResultSort :: Pattern level Variable child -> Sort level
getPatternResultSort (AndPattern p) = andSort p
getPatternResultSort (BottomPattern p) = bottomSort p
getPatternResultSort (CeilPattern p) = ceilResultSort p
getPatternResultSort (DomainValuePattern p) = domainValueSort p
getPatternResultSort (EqualsPattern p) = equalsResultSort p
getPatternResultSort (ExistsPattern p) = existsSort p
getPatternResultSort (FloorPattern p) = floorResultSort p
getPatternResultSort (ForallPattern p) = forallSort p
getPatternResultSort (IffPattern p) = iffSort p
getPatternResultSort (ImpliesPattern p) = impliesSort p
getPatternResultSort (InPattern p) = inResultSort p
getPatternResultSort (NextPattern p) = nextSort p
getPatternResultSort (NotPattern p) = notSort p
getPatternResultSort (OrPattern p) = orSort p
getPatternResultSort (RewritesPattern p) = rewritesSort p
getPatternResultSort (StringLiteralPattern _) = stringMetaSort
getPatternResultSort (CharLiteralPattern _) = charMetaSort
getPatternResultSort (TopPattern p) = topSort p
getPatternResultSort (VariablePattern p) = variableSort p
getPatternResultSort (ApplicationPattern _) =
    error "Application pattern sort currently undefined"
