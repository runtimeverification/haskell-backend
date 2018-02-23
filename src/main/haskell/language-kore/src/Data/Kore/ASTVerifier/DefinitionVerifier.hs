{-|
Module      : Data.Kore.ASTVerifier.DefinitionVerifier
Description : Tools for verifying the wellformedness of a Kore 'Definiton'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
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

{-|'verifyDefinition' verifies the welformedness of a Kore 'Definition'.

It does not handle some cases when combining object sorts with meta patterns or
the other way around.
e.g. for:

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
