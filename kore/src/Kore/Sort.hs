{- |
Module      : Kore.Sort
Description : Kore sorts and sort variables
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

module Kore.Sort
    ( SortVariable (..)
    , SortActual (..)
    , Sort (..)
    , substituteSortVariables
    -- * Meta-sorts
    , MetaSortType (..)
    , MetaBasicSortType (..)
    , metaSortsList
    , metaSortTypeString
    , metaSortsListWithString
    , charMetaSortId
    , charMetaSortActual
    , charMetaSort
    , stringMetaSortId
    , stringMetaSortActual
    , stringMetaSort
    , predicateSortId
    , predicateSortActual
    , predicateSort
    -- * Re-exports
    , module Kore.AST.Identifier
    , module Kore.AST.MetaOrObject
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
                 ( Hashable )
import qualified Data.Map.Strict as Map
import           GHC.Generics
                 ( Generic )

import Kore.AST.Identifier
import Kore.AST.MetaOrObject
import Kore.Unparser

{-|'SortVariable' corresponds to the @object-sort-variable@ and
@meta-sort-variable@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
newtype SortVariable level = SortVariable
    { getSortVariable  :: Id level }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (SortVariable level)

instance NFData (SortVariable level)

instance Unparse (SortVariable level) where
    unparse = unparse . getSortVariable
    unparse2 SortVariable { getSortVariable } = unparse2 getSortVariable

{-|'SortActual' corresponds to the @sort-constructor{sort-list}@ branch of the
@object-sort@ and @meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SortActual level = SortActual
    { sortActualName  :: !(Id level)
    , sortActualSorts :: ![Sort level]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (SortActual level)

instance NFData (SortActual level)

instance Unparse (SortActual level) where
    unparse SortActual { sortActualName, sortActualSorts } =
        unparse sortActualName <> parameters sortActualSorts
    unparse2 SortActual { sortActualName, sortActualSorts } =
        case sortActualSorts of
            [] -> unparse2 sortActualName
            _ -> "("
                  <> unparse2 sortActualName
                  <> " "
                  <> parameters2 sortActualSorts
                  <> ")"

{-|'Sort' corresponds to the @object-sort@ and
@meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data Sort level
    = SortVariableSort !(SortVariable level)
    | SortActualSort !(SortActual level)
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Sort level)

instance NFData (Sort level)

instance Unparse (Sort level) where
    unparse =
        \case
            SortVariableSort sortVariable -> unparse sortVariable
            SortActualSort sortActual -> unparse sortActual
    unparse2 =
        \case
            SortVariableSort sortVariable -> unparse2 sortVariable
            SortActualSort sortActual -> unparse2 sortActual
{- | Substitute sort variables in a 'Sort'.

Sort variables that are not in the substitution are not changed.

 -}
substituteSortVariables
    :: Map.Map (SortVariable level) (Sort level)
    -- ^ Sort substitution
    -> Sort level
    -> Sort level
substituteSortVariables substitution sort =
    case sort of
        SortVariableSort var ->
            case Map.lookup var substitution of
                Just sort' -> sort'
                Nothing -> sort
        SortActualSort sortActual@SortActual { sortActualSorts } ->
            SortActualSort sortActual
                { sortActualSorts =
                    substituteSortVariables substitution <$> sortActualSorts
                }

{-|'MetaSortType' corresponds to the @meta-sort-constructor@ syntactic category
from the Semantics of K, Section 9.1.2 (Sorts).

Ths is not represented directly in the AST, we're using the string
representation instead.
-}
data MetaBasicSortType
    = CharSort
    deriving (Generic)

instance Hashable MetaBasicSortType

data MetaSortType
    = MetaBasicSortType MetaBasicSortType
    | StringSort
    deriving(Generic)

instance Hashable MetaSortType

metaBasicSortsList :: [MetaBasicSortType]
metaBasicSortsList = [ CharSort ]

metaSortsList :: [MetaSortType]
metaSortsList = map MetaBasicSortType metaBasicSortsList

metaSortsListWithString :: [MetaSortType]
metaSortsListWithString = StringSort : metaSortsList

metaBasicSortTypeString :: MetaBasicSortType -> String
metaBasicSortTypeString CharSort        = "Char"

metaSortTypeString :: MetaSortType -> String
metaSortTypeString (MetaBasicSortType s) = metaBasicSortTypeString s
metaSortTypeString StringSort            = "String"

instance Show MetaSortType where
    show sortType = '#' : metaSortTypeString sortType

charMetaSortId :: Id Meta
charMetaSortId = implicitId "#Char"

charMetaSortActual :: SortActual Meta
charMetaSortActual = SortActual charMetaSortId []

charMetaSort :: Sort Meta
charMetaSort = SortActualSort charMetaSortActual

stringMetaSortId :: Id Meta
stringMetaSortId = implicitId "#String"

stringMetaSortActual :: SortActual Meta
stringMetaSortActual = SortActual stringMetaSortId []

stringMetaSort :: Sort Meta
stringMetaSort = SortActualSort stringMetaSortActual

predicateSortId :: Id level
predicateSortId = implicitId "_PREDICATE"

predicateSortActual :: SortActual level
predicateSortActual = SortActual predicateSortId []

{- | Placeholder sort for constructing new predicates.

The final predicate sort is unknown until the predicate is attached to a
pattern.
 -}
predicateSort :: Sort level
{- TODO PREDICATE (thomas.tuegel):

Add a constructor

> data Sort level = ... | FlexibleSort

to use internally as a placeholder where the predicate sort is not yet
known. Using the sort _PREDICATE{} is a kludge; the backend will melt down if
the user tries to define a sort named _PREDICATE{}. (At least, this is not
actually a valid identifier in Kore.)

Until this is fixed, the identifier _PREDICATE is reserved in
Kore.ASTVerifier.DefinitionVerifier.indexImplicitModule.

-}
predicateSort = SortActualSort predicateSortActual
