{-|
Module      : Kore.ASTHelpers
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
module Kore.ASTHelpers
    ( ApplicationSorts (..)
    , symbolOrAliasSorts
    , quantifyFreeVariables
    ) where

import           Data.Foldable
                 ( foldl' )
import           Data.Functor.Foldable
                 ( Fix (..) )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.Sentence
import Kore.Error
import Kore.Variables.Free


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

{-|'quantifyFreeVariables' quantifies all free variables in the given pattern.
It assumes that the pattern has the provided sort.
-}
quantifyFreeVariables
    :: MetaOrObject level
    => Sort level -> CommonPurePattern level -> CommonPurePattern level
quantifyFreeVariables s p =
    foldl'
        (wrapAndQuantify s)
        p
        (checkUnique (pureFreeVariables (Proxy :: Proxy level) p))

wrapAndQuantify
    :: Sort level
    -> CommonPurePattern level
    -> Variable level
    -> CommonPurePattern level
wrapAndQuantify s p var =
    Fix
        (ForallPattern Forall
            { forallSort = s
            , forallVariable = var
            , forallChild = p
            }
        )

checkUnique
    :: Set.Set (Variable level) -> Set.Set (Variable level)
checkUnique variables =
    case checkUniqueEither (Set.toList variables) Map.empty of
        Right _  -> variables
        Left err -> error err

checkUniqueEither
    :: [Variable level]
    -> Map.Map String (Variable level)
    -> Either String ()
checkUniqueEither [] _ = Right ()
checkUniqueEither (var:vars) indexed =
    case Map.lookup name indexed of
        Nothing -> checkUniqueEither vars (Map.insert name var indexed)
        Just existingV ->
            Left
                (  "Conflicting variables: "
                ++ show var
                ++ " and "
                ++ show existingV
                ++ "."
                )
  where
    name = getId (variableName var)
