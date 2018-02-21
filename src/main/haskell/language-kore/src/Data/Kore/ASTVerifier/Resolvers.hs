module Data.Kore.ASTVerifier.Resolvers where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule

import qualified Data.Map                              as Map

resolveSort
    :: (IndexedModule -> Map.Map (Id a) (SortDescription a))
    -> IndexedModule
    -> Id a
    -> Either (Error VerifyError) (SortDescription a)
resolveSort mapExtractor indexedModule sortId =
    case resolveThing mapExtractor indexedModule sortId of
        Nothing -> koreFail ("Sort '" ++ getId sortId ++  "' not declared.")
        Just sortDescription -> Right sortDescription
