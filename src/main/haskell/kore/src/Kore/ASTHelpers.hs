{-|
Module      : Kore.ASTHelpers
Description : Utilities for handling ASTs.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Data.Foldable
                 ( foldl' )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import Kore.AST.Pure
import Kore.AST.Sentence
import Kore.Error
import Kore.Variables.Free


data ApplicationSorts level = ApplicationSorts
    { applicationSortsOperands :: ![Sort level]
    , applicationSortsResult   :: !(Sort level)
    }
    deriving (Eq, Ord, Show)

{-|'symbolOrAliasSorts' builds the return and operand sorts for an application
pattern from the given sort parameters.
-}
symbolOrAliasSorts
    :: (SentenceSymbolOrAlias ssoa, MonadError (Error e) m)
    => [Sort level]
    -> ssoa level pat
    -> m (ApplicationSorts level)
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
    => Map.Map (SortVariable level) (Sort level)
    -> Sort level
    -> m (Sort level)
substituteSortVariables variableToSort (SortVariableSort variable) =
    case Map.lookup variable variableToSort of
        Just sort -> return sort
        Nothing   ->
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
    => [SortVariable level]
    -> [Sort level]
    -> m [(SortVariable level, Sort level)]
pairVariablesToSorts variables sorts
    | variablesLength < sortsLength =
        koreFail "Application uses more sorts than the declaration."
    | variablesLength > sortsLength =
        koreFail "Application uses less sorts than the declaration."
    | otherwise = return (zip variables sorts)
  where
    variablesLength = length variables
    sortsLength = length sorts

{-|'quantifyFreeVariables' quantifies all free variables in the given pattern.
It assumes that the pattern has the provided sort.
-}
quantifyFreeVariables
    :: (Foldable domain, Functor domain, MetaOrObject level)
    => Sort level
    -> CommonPurePattern level domain
    -> CommonPurePattern level domain
quantifyFreeVariables s p =
    foldl'
        (wrapAndQuantify s)
        p
        (checkUnique (freePureVariables p))

wrapAndQuantify
    :: Functor domain
    => Sort level
    -> CommonPurePattern level domain
    -> Variable level
    -> CommonPurePattern level domain
wrapAndQuantify s p var =
    asPurePattern
        (mempty :< ForallPattern Forall
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
    -> Map.Map Text (Variable level)
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
