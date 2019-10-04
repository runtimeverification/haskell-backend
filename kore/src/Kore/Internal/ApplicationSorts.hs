{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.ApplicationSorts
    ( ApplicationSorts (..)
    , applicationSorts
    , symbolOrAliasSorts
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Function
import Data.Hashable
    ( Hashable
    )
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Error
import Kore.Sort hiding
    ( substituteSortVariables
    )
import Kore.Syntax.Sentence

data ApplicationSorts = ApplicationSorts
    { applicationSortsOperands :: ![Sort]
    , applicationSortsResult   :: !Sort
    }
    deriving (Eq, GHC.Generic, Ord, Show)

instance NFData ApplicationSorts

instance Hashable ApplicationSorts

instance SOP.Generic ApplicationSorts

instance SOP.HasDatatypeInfo ApplicationSorts

instance Debug ApplicationSorts

instance Diff ApplicationSorts

applicationSorts :: [Sort] -> Sort -> ApplicationSorts
applicationSorts = ApplicationSorts

{-|'symbolOrAliasSorts' builds the return and operand sorts for an application
pattern from the given sort parameters.
-}
symbolOrAliasSorts
    :: (SentenceSymbolOrAlias sentence, MonadError (Error e) m)
    => [Sort]
    -> sentence pat
    -> m ApplicationSorts
symbolOrAliasSorts params sentence = do
    variableToSort <-
        pairVariablesToSorts
            paramVariables
            params
    fullReturnSort <-
        substituteSortVariables
            (Map.fromList variableToSort)
            parametrizedReturnSort
    operandSorts <-
        mapM
            (substituteSortVariables (Map.fromList variableToSort))
            parametrizedArgumentSorts
    return ApplicationSorts
        { applicationSortsOperands = operandSorts
        , applicationSortsResult = fullReturnSort
        }
  where
    paramVariables = getSentenceSymbolOrAliasSortParams sentence
    parametrizedArgumentSorts = getSentenceSymbolOrAliasArgumentSorts sentence
    parametrizedReturnSort = getSentenceSymbolOrAliasResultSort sentence

substituteSortVariables
    :: MonadError (Error e) m
    => Map SortVariable Sort
    -> Sort
    -> m Sort
substituteSortVariables variableToSort (SortVariableSort variable) =
    Map.lookup variable variableToSort
    & maybe missingSortVariable return
  where
    missingSortVariable =
        koreFail
            (  "Sort variable not found: '"
            ++ getIdForError (getSortVariable variable)
            ++ "'."
            )
substituteSortVariables
    variableToSort
    (SortActualSort sort@SortActual { sortActualSorts = sortList })
  = do
    substituted <- mapM (substituteSortVariables variableToSort) sortList
    return (SortActualSort sort { sortActualSorts = substituted })

pairVariablesToSorts
    :: MonadError (Error e) m
    => [SortVariable]
    -> [Sort]
    -> m [(SortVariable, Sort)]
pairVariablesToSorts variables sorts
    | variablesLength < sortsLength =
        koreFail "Application uses more sorts than the declaration."
    | variablesLength > sortsLength =
        koreFail "Application uses less sorts than the declaration."
    | otherwise = return (zip variables sorts)
  where
    variablesLength = length variables
    sortsLength = length sorts
