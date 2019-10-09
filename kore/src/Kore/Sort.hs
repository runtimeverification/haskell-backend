{- |
Copyright   : (c) Runtime Verification, 2018

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

module Kore.Sort
    ( SortVariable (..)
    , SortActual (..)
    , Sort (..)
    , getSortId
    , sortSubstitution
    , substituteSortVariables
    , rigidSort
    , sameSort
    , matchSort
    , matchSorts
    , alignSorts
    -- * Meta-sorts
    , MetaSortType (..)
    , metaSort
    , metaSortTypeString
    , metaSortsListWithString
    , stringMetaSortId
    , stringMetaSortActual
    , stringMetaSort
    , predicateSortId
    , predicateSortActual
    , predicateSort
    -- * Exceptions
    , SortMismatch (..)
    , sortMismatch
    , MissingArgument (..)
    , missingArgument
    , UnexpectedArgument (..)
    , unexpectedArgument
    -- * Re-exports
    , module Kore.Syntax.Id
    ) where

import Control.DeepSeq
    ( NFData
    )
import Control.Exception
    ( Exception (..)
    , throw
    )
import Data.Align
import qualified Data.Foldable as Foldable
import Data.Hashable
    ( Hashable
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( fromMaybe
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.These
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Syntax.Id
import Kore.Unparser

{- | @SortVariable@ is a Kore sort variable.

@SortVariable@ corresponds to the @sort-variable@ syntactic category from the
Semantics of K, Section 9.1.2 (Sorts).

 -}
newtype SortVariable = SortVariable
    { getSortVariable  :: Id }
    deriving (Show, Eq, Ord, GHC.Generic)

instance Hashable SortVariable

instance NFData SortVariable

instance Unparse SortVariable where
    unparse = unparse . getSortVariable
    unparse2 SortVariable { getSortVariable } = unparse2 getSortVariable

instance SOP.Generic SortVariable

instance SOP.HasDatatypeInfo SortVariable

instance Debug SortVariable

instance Diff SortVariable

{-|'SortActual' corresponds to the @sort-constructor{sort-list}@ branch of the
@object-sort@ and @meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

-}
data SortActual = SortActual
    { sortActualName  :: !Id
    , sortActualSorts :: ![Sort]
    }
    deriving (Show, Eq, Ord, GHC.Generic)

instance Hashable SortActual

instance NFData SortActual

instance SOP.Generic SortActual

instance SOP.HasDatatypeInfo SortActual

instance Debug SortActual

instance Diff SortActual

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
    deriving (Show, Eq, Ord, GHC.Generic)

instance Hashable Sort

instance NFData Sort

instance SOP.Generic Sort

instance SOP.HasDatatypeInfo Sort

instance Debug Sort

instance Diff Sort

instance Unparse Sort where
    unparse =
        \case
            SortVariableSort sortVariable -> unparse sortVariable
            SortActualSort sortActual -> unparse sortActual
    unparse2 =
        \case
            SortVariableSort sortVariable -> unparse2 sortVariable
            SortActualSort sortActual -> unparse2 sortActual

getSortId :: Sort -> Id
getSortId =
    \case
        SortVariableSort SortVariable { getSortVariable } ->
            getSortVariable
        SortActualSort SortActual { sortActualName } ->
            sortActualName

{- | The 'Sort' substitution from applying the given sort parameters.
 -}
sortSubstitution
    :: [SortVariable]
    -> [Sort]
    -> Map.Map SortVariable Sort
sortSubstitution variables sorts =
    Foldable.foldl' insertSortVariable Map.empty (align variables sorts)
  where
    insertSortVariable map' =
        \case
            These var sort -> Map.insert var sort map'
            This _ ->
                (error . show . Pretty.vsep) ("Too few parameters:" : expected)
            That _ ->
                (error . show . Pretty.vsep) ("Too many parameters:" : expected)
    expected =
        [ "Expected:"
        , Pretty.indent 4 (parameters variables)
        , "but found:"
        , Pretty.indent 4 (parameters sorts)
        ]

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
            fromMaybe sort $ Map.lookup var substitution
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
data MetaSortType
    = StringSort
    deriving (GHC.Generic)

instance Hashable MetaSortType

metaSortsListWithString :: [MetaSortType]
metaSortsListWithString = [StringSort]

metaSortTypeString :: MetaSortType -> String
metaSortTypeString StringSort            = "String"

instance Show MetaSortType where
    show sortType = '#' : metaSortTypeString sortType

metaSort :: MetaSortType -> Sort
metaSort = \case
    StringSort -> stringMetaSort

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

rigidSort :: Sort -> Maybe Sort
rigidSort sort
  | sort == predicateSort = Nothing
  | otherwise             = Just sort

data SortMismatch = SortMismatch !Sort !Sort
    deriving (Eq, Show, Typeable)

instance Exception SortMismatch where
    displayException (SortMismatch sort1 sort2) =
        (show . Pretty.vsep)
            [ "Could not make sort"
            , Pretty.indent 4 (unparse sort2)
            , "match sort"
            , Pretty.indent 4 (unparse sort1)
            , "This is a program bug!"
            ]

{- | Throw a 'SortMismatch' exception.
 -}
sortMismatch :: Sort -> Sort -> a
sortMismatch sort1 sort2 = throw (SortMismatch sort1 sort2)

newtype MissingArgument = MissingArgument Sort
    deriving (Eq, Show, Typeable)

instance Exception MissingArgument  where
    displayException (MissingArgument sort1) =
        (show . Pretty.sep)
            [ "Expected another argument of sort"
            , unparse sort1
            ]

newtype UnexpectedArgument = UnexpectedArgument Sort
    deriving (Eq, Show, Typeable)

instance Exception UnexpectedArgument where
    displayException (UnexpectedArgument sort2) =
        (show . Pretty.sep)
            [ "Unexpected argument of sort"
            , unparse sort2
            ]

missingArgument :: Sort -> a
missingArgument sort1 = throw (MissingArgument sort1)

unexpectedArgument :: Sort -> a
unexpectedArgument sort2 = throw (UnexpectedArgument sort2)

{- | Throw an error if two sorts are not the same, or return the first sort.
 -}
sameSort :: Sort -> Sort -> Sort
sameSort sort1 sort2
  | sort1 == sort2 = sort1
  | otherwise = sortMismatch sort1 sort2

{- | Match the second sort to the first.

If the second sort is flexible, it matches the first sort. If the second sort is
rigid, it must be equal to the first sort.

 -}
matchSort :: Sort -> Sort -> Sort
matchSort sort1 sort2 =
    maybe sort1 (sameSort sort1) (rigidSort sort2)

matchSorts :: [Sort] -> [Sort] -> [Sort]
matchSorts = alignWith matchTheseSorts
  where
    matchTheseSorts (This sort1) = missingArgument sort1
    matchTheseSorts (That sort2) = unexpectedArgument sort2
    matchTheseSorts (These sort1 sort2) = matchSort sort1 sort2

alignSorts :: Foldable f => f Sort -> Sort
alignSorts = fromMaybe predicateSort . Foldable.foldl' worker Nothing
  where
    worker Nothing      sort2 = rigidSort sort2
    worker (Just sort1) sort2 =
        Just $ maybe sort1 (alignSort sort1) (rigidSort sort2)
    alignSort sort1 sort2
      | sort1 == sort2 = sort1
      | otherwise = sortMismatch sort1 sort2
