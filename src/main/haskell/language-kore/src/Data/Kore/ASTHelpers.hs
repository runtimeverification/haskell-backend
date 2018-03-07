module Data.Kore.ASTHelpers (ApplicationSorts (..), symbolOrAliasSorts) where

import           Data.Kore.AST
import           Data.Kore.Error

import qualified Data.Map        as Map

data ApplicationSorts a = ApplicationSorts
    { applicationSortsOperands :: ![Sort a]
    , applicationSortsResult   :: !(Sort a)
    }
    deriving (Show, Eq)

{-|'symbolOrAliasSorts' builds the return and operand sorts for an application
pattern from the given sort parameters.
-}
symbolOrAliasSorts
    :: (SentenceSymbolOrAlias ssoa)
    => [Sort a]
    -> ssoa a
    -> Either (Error b) (ApplicationSorts a)
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
    :: Map.Map (SortVariable a) (Sort a)
    -> Sort a
    -> Either (Error b) (Sort a)
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
    :: [SortVariable a]
    -> [Sort a]
    -> Either (Error b) [(SortVariable a, Sort a)]
pairVariablesToSorts variables sorts
    | variablesLength < sortsLength =
        koreFail "Application uses more sorts than the declaration."
    | variablesLength > sortsLength =
        koreFail "Application uses less sorts than the declaration."
    | otherwise = Right (zip variables sorts)
  where
    variablesLength = length variables
    sortsLength = length sorts
