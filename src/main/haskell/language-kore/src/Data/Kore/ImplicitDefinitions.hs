{-|
Module      : Data.Kore.ImplicitDefinitions
Description : Implicit definitions for Kore.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ImplicitDefinitions where

import           Data.Kore.AST.Common

charMetaSort :: Sort Meta
charMetaSort = metaSort CharSort
charListMetaSort :: Sort Meta
charListMetaSort = metaSort CharListSort
patternMetaSort :: Sort Meta
patternMetaSort = metaSort PatternSort
patternListMetaSort :: Sort Meta
patternListMetaSort = metaSort PatternListSort
sortMetaSort :: Sort Meta
sortMetaSort = metaSort SortSort
sortListMetaSort :: Sort Meta
sortListMetaSort = metaSort SortListSort
symbolMetaSort :: Sort Meta
symbolMetaSort = metaSort SymbolSort
symbolListMetaSort :: Sort Meta
symbolListMetaSort = metaSort SymbolListSort
variableMetaSort :: Sort Meta
variableMetaSort = metaSort VariableSort
variableListMetaSort :: Sort Meta
variableListMetaSort = metaSort VariableListSort

metaSort :: MetaSortType -> Sort Meta
metaSort sortType =
    SortActualSort SortActual
        { sortActualName = Id (show sortType)
        , sortActualSorts = []}
