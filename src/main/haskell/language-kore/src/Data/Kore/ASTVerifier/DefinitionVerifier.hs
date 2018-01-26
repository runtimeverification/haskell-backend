module Data.Kore.ASTVerifier.DefinitionVerifier (verifyDefinition) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.ModuleVerifier
import           Data.Kore.ASTVerifier.IndexedModule
import           Data.Kore.Error
import qualified Data.Set as Set

verifyDefinition :: Definition -> Either (Error VerifyError) VerifySuccess
verifyDefinition definition = do
    verifyUniqueNames koreModule defaultNames
    let indexedModule = indexModule koreModule defaultIndexedModule
    verifyModule koreModule indexedModule
    verifyAttributes
        (definitionAttributes definition) defaultIndexedModule Set.empty
  where
    koreModule = definitionModules definition
    (defaultIndexedModule, defaultNames) =
        implicitIndexedModule (ModuleName "Dummy module")
