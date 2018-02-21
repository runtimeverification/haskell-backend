module Data.Kore.ASTVerifier.ModuleVerifier
    (verifyModule, verifyUniqueNames) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.Resolvers
import qualified Data.Kore.ASTVerifier.SentenceVerifier   as SentenceVerifier
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule

import qualified Data.Set                                 as Set

verifyUniqueNames
    :: Set.Set String
    -> Module
    -> Either (Error VerifyError) (Set.Set String)
verifyUniqueNames existingNames koreModule =
    withContext
        ("module '" ++ getModuleName (moduleName koreModule) ++ "'")
        (SentenceVerifier.verifyUniqueNames
            (moduleSentences koreModule)
            existingNames)

verifyModule
    :: IndexedModule
    -> Either (Error VerifyError) VerifySuccess
verifyModule indexedModule =
    withContext
        ("module '" ++ getModuleName (indexedModuleName indexedModule) ++ "'")
        (do
            verifyAttributes
                (indexedModuleAttributes indexedModule) indexedModule Set.empty
            SentenceVerifier.verifySentences
                (resolveSort indexedModuleObjectSortDescriptions indexedModule)
                (resolveSort indexedModuleMetaSortDescriptions indexedModule)
                indexedModule
                (indexedModuleRawSentences indexedModule)
        )
