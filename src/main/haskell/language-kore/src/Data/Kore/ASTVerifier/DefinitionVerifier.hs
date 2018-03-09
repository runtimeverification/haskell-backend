{-|
Module      : Data.Kore.ASTVerifier.DefinitionVerifier
Description : Tools for verifying the wellformedness of a Kore 'Definiton'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.DefinitionVerifier (verifyDefinition, verifyKoreDefinition) where

import           Control.Monad                            (foldM, foldM_)
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.ModuleVerifier
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitKore
import           Data.Kore.IndexedModule.IndexedModule

import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set

{-|'verifyDefinition' verifies the welformedness of a Kore 'Definition'.

It does not fully verify the validity of object-meta combinations of patterns,
e.g.:

@
  axiom{S1,S2,R}
    \equals{Ctxt{S1,S2},R}(
      gamma{S1,S2}(
        #variableToPattern{}(#X:#Variable{}),
        #P:#Pattern{}),
      \exists{Ctxt{S1,S2}}(
        #X:#Variable{},
        gamma0{S1,S2}(
          #variableToPattern{}(#X:#Variable{}),
          #P:#Pattern{}))) []
@

-}
verifyDefinition :: Definition -> Either (Error VerifyError) VerifySuccess
verifyDefinition definition = do
    defaultNames <- verifyUniqueNames sortNames implicitModule
    foldM_ verifyUniqueNames defaultNames (definitionModules definition)

    implicitIndexedModules <-
        indexModuleIfNeeded
            moduleWithMetaSorts
            nameToModule
            (Map.singleton defaultModuleName defaultModuleWithMetaSorts)
            implicitModule
    let
        implicitIndexedModule =
            case
                Map.lookup (moduleName implicitModule) implicitIndexedModules
            of
                Just m -> m
    indexedModules <-
        foldM
            (indexModuleIfNeeded
                (ImplicitIndexedModule implicitIndexedModule)
                nameToModule
            )
            implicitIndexedModules
            (definitionModules definition)
    mapM_ verifyModule (Map.elems indexedModules)
    verifyAttributes
        (definitionAttributes definition) implicitIndexedModule Set.empty
  where
    defaultModuleName = ModuleName "Default module"
    (moduleWithMetaSorts, sortNames) =
        indexedModuleWithMetaSorts defaultModuleName
    getIndexedModule (ImplicitIndexedModule im) = im
    defaultModuleWithMetaSorts = getIndexedModule moduleWithMetaSorts
    implicitModule = uncheckedKoreModule
    nameToModule =
        Map.fromList
            (map (\m -> (moduleName m, m)) (definitionModules definition))

{-|'verifyKoreDefinition' is meant to be used only in the
'Data.Kore.Implicit' package. It verifies the correctness of a definition
containing only the 'kore' default module.
-}
verifyKoreDefinition :: Definition -> Either (Error VerifyError) VerifySuccess
verifyKoreDefinition definition =
    -- VerifyDefinition already checks the Kore module, so we skip it.
    verifyDefinition definition { definitionModules = [] }
