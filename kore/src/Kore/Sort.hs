{- |
Copyright   : (c) Runtime Verification, 2018

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
    , module Kore.Syntax.Id
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
                 ( Hashable )
import qualified Data.Map.Strict as Map
import           GHC.Generics
                 ( Generic )

import Kore.Syntax.Id
import Kore.Unparser

{- | @SortVariable@ is a Kore sort variable.

@SortVariable@ corresponds to the @sort-variable@ syntactic category from the
Semantics of K, Section 9.1.2 (Sorts).

 -}
newtype SortVariable = SortVariable
    { getSortVariable  :: Id }
    deriving (Show, Eq, Ord, Generic)

instance Hashable SortVariable

instance NFData SortVariable

instance Unparse SortVariable where
    unparse = unparse . getSortVariable
    unparse2 SortVariable { getSortVariable } = unparse2 getSortVariable

{-|'SortActual' corresponds to the @sort-constructor{sort-list}@ branch of the
@object-sort@ and @meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

-}
data SortActual = SortActual
    { sortActualName  :: !Id
    , sortActualSorts :: ![Sort]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable SortActual

instance NFData SortActual

instance Unparse SortActual where
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

-}
data Sort
    = SortVariableSort !SortVariable
    | SortActualSort !SortActual
    deriving (Show, Eq, Ord, Generic)

instance Hashable Sort

instance NFData Sort

instance Unparse Sort where
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
    :: Map.Map SortVariable Sort
    -- ^ Sort substitution
    -> Sort
    -> Sort
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

charMetaSortId :: Id
charMetaSortId = implicitId "#Char"

charMetaSortActual :: SortActual
charMetaSortActual = SortActual charMetaSortId []

charMetaSort :: Sort
charMetaSort = SortActualSort charMetaSortActual

stringMetaSortId :: Id
stringMetaSortId = implicitId "#String"

stringMetaSortActual :: SortActual
stringMetaSortActual = SortActual stringMetaSortId []

stringMetaSort :: Sort
stringMetaSort = SortActualSort stringMetaSortActual

predicateSortId :: Id
predicateSortId = implicitId "_PREDICATE"

predicateSortActual :: SortActual
predicateSortActual = SortActual predicateSortId []

{- | Placeholder sort for constructing new predicates.

The final predicate sort is unknown until the predicate is attached to a
pattern.
 -}
predicateSort :: Sort
{- TODO PREDICATE (thomas.tuegel):

Add a constructor

> data Sort = ... | FlexibleSort

to use internally as a placeholder where the predicate sort is not yet
known. Using the sort _PREDICATE{} is a kludge; the backend will melt down if
the user tries to define a sort named _PREDICATE{}. (At least, this is not
actually a valid identifier in Kore.)

Until this is fixed, the identifier _PREDICATE is reserved in
Kore.ASTVerifier.DefinitionVerifier.indexImplicitModule.

-}
predicateSort = SortActualSort predicateSortActual
