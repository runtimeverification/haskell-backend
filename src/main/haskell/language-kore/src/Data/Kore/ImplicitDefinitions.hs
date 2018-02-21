module Data.Kore.ImplicitDefinitions where

import           Data.Kore.AST

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
stringMetaSort :: Sort Meta
stringMetaSort = metaSort StringSort
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
