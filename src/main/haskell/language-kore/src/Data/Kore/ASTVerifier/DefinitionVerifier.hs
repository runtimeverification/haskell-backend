{-|
Module      : Data.Kore.ASTVerifier.DefinitionVerifier
Description : Tools for verifying the wellformedness of a Kore 'Definiton'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.DefinitionVerifier
    ( defaultAttributesVerification
    , verifyDefinition
    , verifyAndIndexDefinition
    , verifyImplicitKoreDefinition
    , verifyNormalKoreDefinition
    , AttributesVerification (..)
    ) where

import           Control.Monad                            (foldM, foldM_)
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.ModuleVerifier
import           Data.Kore.Error
import           Data.Kore.Implicit.Definitions           (uncheckedAttributesDefinition,
                                                           uncheckedKoreModules)
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
verifyDefinition
    :: AttributesVerification
    -> KoreDefinition
    -> Either (Error VerifyError) VerifySuccess
verifyDefinition attributesVerification definition = do
    verifyAndIndexDefinition attributesVerification definition
    verifySuccess

{-|'verifyAndIndexDefinition' verifies a definition and returns an indexed
collection of the definition's modules.
-}
verifyAndIndexDefinition
    :: AttributesVerification
    -> KoreDefinition
    -> Either (Error VerifyError) (Map.Map ModuleName KoreIndexedModule)
verifyAndIndexDefinition attributesVerification definition = do
    (implicitIndexedModules, implicitIndexedModule, defaultNames) <-
        indexImplicitModules

    foldM_ verifyUniqueNames defaultNames (definitionModules definition)

    indexedModules <-
        foldM
            (indexModuleIfNeeded
                implicitIndexedModule
                nameToModule
            )
            implicitIndexedModules
            (definitionModules definition)
    mapM_ (verifyModule attributesVerification) (Map.elems indexedModules)
    verifyAttributes
        (definitionAttributes definition)
        attributesVerification
    return indexedModules
  where
    nameToModule =
        Map.fromList
            (map (\m -> (moduleName m, m)) (definitionModules definition))

defaultAttributesVerification
    :: Either (Error VerifyError) AttributesVerification
defaultAttributesVerification =
    VerifyAttributes
        <$> verifyNormalKoreDefinition
            DoNotVerifyAttributes uncheckedAttributesDefinition

indexImplicitModules
    :: Either
        (Error VerifyError)
        ( Map.Map ModuleName KoreIndexedModule
        , KoreImplicitIndexedModule
        , Set.Set String
        )
indexImplicitModules = do
    defaultNames <- foldM verifyUniqueNames sortNames uncheckedKoreModules
    (indexedModules, defaultModule) <- foldM
        indexImplicitModule
        ( Map.singleton defaultModuleName defaultModuleWithMetaSorts
        , moduleWithMetaSorts
        )
        uncheckedKoreModules
    return (indexedModules, defaultModule, defaultNames)
  where
    defaultModuleName = ModuleName "Default module"
    getIndexedModule (ImplicitIndexedModule im) = im
    defaultModuleWithMetaSorts = getIndexedModule moduleWithMetaSorts
    (moduleWithMetaSorts, sortNames) =
        indexedModuleWithMetaSorts defaultModuleName

{-|'verifyNormalKoreDefinition' is meant to be used only in the
'Data.Kore.Implicit' package. It verifies the correctness of a definition
containing only the 'kore' default module.
-}
verifyNormalKoreDefinition
    :: AttributesVerification
    -> KoreDefinition
    -> Either (Error VerifyError) KoreIndexedModule
verifyNormalKoreDefinition attributesVerification definition = do
    -- VerifyDefinition already checks the Kore module, so we skip it.
    modules <-
        verifyAndIndexDefinition
            attributesVerification
            definition
    name <- extractSingleModuleNameFromDefinition definition
    findModule name modules

{-|'verifyImplicitKoreDefinition' is meant to be used only in the
'Data.Kore.Implicit' package. It verifies the correctness of a definition
containing only the 'kore' default module.
-}
verifyImplicitKoreDefinition
    :: AttributesVerification
    -> KoreDefinition
    -> Either (Error VerifyError) KoreIndexedModule
verifyImplicitKoreDefinition attributesVerification definition = do
    modules <-
        verifyAndIndexDefinition
            attributesVerification
            definition { definitionModules = [] }
    name <- extractSingleModuleNameFromDefinition definition
    findModule name modules

extractSingleModuleNameFromDefinition
    :: KoreDefinition
    -> Either (Error VerifyError) ModuleName
extractSingleModuleNameFromDefinition definition =
    case definitionModules definition of
        [] ->
            koreFail
                (  "The kore implicit definition should have exactly"
                ++ " one module, but found none."
                )
        [a] -> return (moduleName a)
        _ ->
            koreFail
                (  "The kore implicit definition should have exactly"
                ++ " one module, but found multiple ones."
                )

findModule
    :: ModuleName
    -> Map.Map ModuleName KoreIndexedModule
    -> Either (Error VerifyError) KoreIndexedModule
findModule name modules =
    case Map.lookup name modules of
        Just a -> return a
        Nothing ->
            koreFail
                (  "Internal error: the kore module ("
                ++ show name
                ++ ") was not indexed ("
                ++ show (Map.keys modules)
                ++ ")."
                )
