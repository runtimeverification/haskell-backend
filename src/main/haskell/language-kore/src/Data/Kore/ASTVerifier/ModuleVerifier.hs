module Data.Kore.ASTVerifier.ModuleVerifier (verifyModule,
                                             verifyUniqueNames) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import qualified Data.Kore.ASTVerifier.SentenceVerifier as SentenceVerifier
import           Data.Kore.Error
import qualified Data.Map as Map
import qualified Data.Set as Set

verifyUniqueNames
    :: Module
    -> Set.Set String
    -> Either (Error VerifyError) (Set.Set String)
verifyUniqueNames koreModule existingNames =
    withContext
        ("module '" ++ getModuleName (moduleName koreModule) ++ "'")
        (SentenceVerifier.verifyUniqueNames
            (moduleSentences koreModule)
            existingNames)

verifyModule
    :: Module
    -> IndexedModule
    -> Either (Error VerifyError) VerifySuccess
verifyModule koreModule indexedModule =
    withContext
        ("module '" ++ getModuleName (moduleName koreModule) ++ "'")
        (do
            verifyAttributes
                (moduleAttributes koreModule) indexedModule Set.empty
            SentenceVerifier.verifySentences
                (findObjectSortDescription indexedModule)
                (findMetaSortDescription indexedModule)
                indexedModule
                (moduleSentences koreModule)
        )

findObjectSortDescription
    :: IndexedModule
    -> Id Object
    -> Either (Error VerifyError) (SortDescription Object)
findObjectSortDescription indexedModule id1 =
    findSortDescription id1 (indexedModuleObjectSortDescriptions indexedModule)

findMetaSortDescription
    :: IndexedModule
    -> Id Meta
    -> Either (Error VerifyError) (SortDescription Meta)
findMetaSortDescription indexedModule id1 =
    findSortDescription id1 (indexedModuleMetaSortDescriptions indexedModule)

findSortDescription
    :: Id a
    -> Map.Map (Id a) (SortDescription a)
    -> Either (Error VerifyError) (SortDescription a)
findSortDescription sortId sortIdToSortDescription =
    case Map.lookup sortId sortIdToSortDescription of
        Nothing ->
            Left (koreError ("Sort '" ++ getId sortId ++ "' not declared."))
        Just description -> Right description
