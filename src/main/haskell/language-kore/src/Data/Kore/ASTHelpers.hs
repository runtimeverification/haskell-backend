{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.ASTHelpers
Description : Utilities for handling ASTs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

Each time a function is added to this file, one should consider putting it in a
more specific file. Also, one should consider extracting groups of functions in
more specific files.
-}
module Data.Kore.ASTHelpers ( ApplicationSorts (..)
                            , symbolOrAliasSorts
                            ) where

import           Data.Kore.AST.Common
import           Data.Kore.Error

import qualified Data.Map             as Map

data ApplicationSorts level = ApplicationSorts
    { applicationSortsOperands :: ![Sort level]
    , applicationSortsResult   :: !(Sort level)
    }
    deriving (Show, Eq)

{-|'symbolOrAliasSorts' builds the return and operand sorts for an application
pattern from the given sort parameters.
-}
symbolOrAliasSorts
    :: (SentenceSymbolOrAlias ssoa)
    => [Sort level]
    -> ssoa level pat variable
    -> Either (Error b) (ApplicationSorts level)
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
    :: Map.Map (SortVariable level) (Sort level)
    -> Sort level
    -> Either (Error b) (Sort level)
substituteSortVariables variableToSort (SortVariableSort variable) =
    case Map.lookup variable variableToSort of
        Just sort -> Right sort
        Nothing   ->
            koreFail
                (  "Sort variable not found: '"
                ++ getId (getSortVariable variable)
                ++ "'."
                )
substituteSortVariables
    variableToSort
    (SortActualSort sort@SortActual { sortActualSorts = sortList })
  = do
    substituted <- mapM (substituteSortVariables variableToSort) sortList
    return (SortActualSort sort { sortActualSorts = substituted })

pairVariablesToSorts
    :: [SortVariable level]
    -> [Sort level]
    -> Either (Error b) [(SortVariable level, Sort level)]
pairVariablesToSorts variables sorts
    | variablesLength < sortsLength =
        koreFail "Application uses more sorts than the declaration."
    | variablesLength > sortsLength =
        koreFail "Application uses less sorts than the declaration."
    | otherwise = Right (zip variables sorts)
  where
    variablesLength = length variables
    sortsLength = length sorts
