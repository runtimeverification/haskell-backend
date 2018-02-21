module Data.Kore.ASTVerifier.DefinitionVerifier (verifyDefinition) where

import           Control.Monad                            (foldM, foldM_)
import           Data.Kore.AST
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.ModuleVerifier
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set

verifyDefinition :: Definition -> Either (Error VerifyError) VerifySuccess
verifyDefinition definition = do
    foldM_ verifyUniqueNames defaultNames (definitionModules definition)
    indexedModules <-
        foldM
            (indexModuleIfNeeded defaultIndexedModule nameToModule)
            (Map.singleton defaultModuleName defaultModule)
            (definitionModules definition)
    mapM_ verifyModule (Map.elems indexedModules)
    verifyAttributes
        (definitionAttributes definition) defaultModule Set.empty
  where
    defaultModuleName = ModuleName "Default module"
    (defaultIndexedModule, defaultNames) =
        implicitIndexedModule defaultModuleName
    getIndexedModule (ImplicitIndexedModule im) = im
    defaultModule = getIndexedModule defaultIndexedModule
    nameToModule =
        Map.fromList
            (map (\m -> (moduleName m, m)) (definitionModules definition))
