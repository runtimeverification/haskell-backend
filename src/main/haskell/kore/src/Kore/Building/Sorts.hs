{-|
Module      : Kore.Building.Sorts
Description : Builders for meta sorts and sort variables.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Building.Sorts
    ( AsSort
    , MetaSort
    , ObjectSort
    , CharSort (CharSort)
    , CharListSort (CharListSort)
    , PatternSort (PatternSort)
    , PatternListSort (PatternListSort)
    , SortSort (SortSort)
    , SortListSort (SortListSort)
    , VariableSort
    , VariableListSort
    , MetaSortVariable1 (MetaSortVariable1)
    , asMetaSortVariable
    , ObjectSortVariable1 (ObjectSortVariable1)
    ) where

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.Building.AsAst
import Kore.Implicit.ImplicitSorts

type AsSort level = AsAst (Sort level)
type MetaSort = AsSort Meta
type ObjectSort = AsSort Object

data CharSort = CharSort
instance AsAst (Sort Meta) CharSort where
    asAst _ = charMetaSort

data CharListSort = CharListSort
instance AsAst (Sort Meta) CharListSort where
    asAst _ = charListMetaSort

data PatternSort = PatternSort
instance AsAst (Sort Meta) PatternSort where
    asAst _ = patternMetaSort

data PatternListSort = PatternListSort
instance AsAst (Sort Meta) PatternListSort where
    asAst _ = patternListMetaSort

data SortSort = SortSort
instance AsAst (Sort Meta) SortSort where
    asAst _ = sortMetaSort

data SortListSort = SortListSort
instance AsAst (Sort Meta) SortListSort where
    asAst _ = sortListMetaSort

data VariableSort
instance AsAst (Sort Meta) VariableSort where
    asAst _ = variableMetaSort

data VariableListSort
instance AsAst (Sort Meta) VariableListSort where
    asAst _ = variableListMetaSort

-- TODO(virgil): rename. Also, it is likely that each variable should have sort
-- distinct type.
data MetaSortVariable1 = MetaSortVariable1
    { metaSortVariableName     :: String
    , metaSortVariableLocation :: AstLocation
    }
instance AsAst (Sort Meta) MetaSortVariable1 where
    asAst v = SortVariableSort (asMetaSortVariable v)
asMetaSortVariable :: MetaSortVariable1 -> SortVariable Meta
asMetaSortVariable
    MetaSortVariable1
        { metaSortVariableName = name'
        , metaSortVariableLocation = location
        }
  =
    SortVariable Id
        { getId = name'
        , idLocation = location
        }

data ObjectSortVariable1 = ObjectSortVariable1
    { objectSortVariableName     :: String
    , objectSortVariableLocation :: AstLocation
    }
instance AsAst (Sort Object) ObjectSortVariable1 where
    asAst
        ObjectSortVariable1
            { objectSortVariableName = name'
            , objectSortVariableLocation = location
            }
      =
        SortVariableSort
            (SortVariable Id
                { getId = name'
                , idLocation = location
                }
            )
