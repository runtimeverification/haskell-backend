{-|
Module      : Kore.ASTVerifier.DefinitionVerifier
Description : Tools for verifying the wellformedness of a Kore 'Definiton'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.DefinitionVerifier
    ( defaultAttributesVerification
    , verifyDefinition
    , verifyAndIndexDefinition
    , verifyAndIndexDefinitionWithBase
    , verifyImplicitKoreDefinition
    , verifyNormalKoreDefinition
    , AttributesVerification (..)
    ) where

import           Control.Monad
                 ( foldM )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy )
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.Sentence
import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.ModuleVerifier
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.Implicit.Definitions
                 ( uncheckedKoreModules )
import           Kore.IndexedModule.IndexedModule

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
    :: ParseAttributes atts
    => AttributesVerification atts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) VerifySuccess
verifyDefinition attributesVerification builtinVerifiers definition = do
    _ <- verifyAndIndexDefinition attributesVerification builtinVerifiers definition
    verifySuccess

{-|'verifyAndIndexDefinition' verifies a definition and returns an indexed
collection of the definition's modules.
-}
verifyAndIndexDefinition
    :: ParseAttributes atts
    => AttributesVerification atts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) (Map.Map ModuleName (KoreIndexedModule atts))
verifyAndIndexDefinition attributesVerification builtinVerifiers definition = do
    (indexedModules, _defaultNames) <-
        verifyAndIndexDefinitionWithBase
            Nothing
            attributesVerification
            builtinVerifiers
            definition
    return indexedModules

{-|Verifies a `KoreDefinition` against a preverified definition, consisting of
map of indexed modules and a map of defined names.

If verification is successfull, it returns the updated maps op indexed modules
and defined names.
-}
verifyAndIndexDefinitionWithBase
    :: ParseAttributes atts
    => Maybe
        ( Map.Map ModuleName (KoreIndexedModule atts)
        , Map.Map Text AstLocation
        )
    -> AttributesVerification atts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError)
        ( Map.Map ModuleName (KoreIndexedModule atts)
        , Map.Map Text AstLocation
        )
verifyAndIndexDefinitionWithBase
    maybeBaseDefinition
    attributesVerification
    builtinVerifiers
    definition
  = do
    (implicitModules, implicitModule, defaultNames) <- indexImplicitModules
    let
        (baseIndexedModules, baseNames) =
            case maybeBaseDefinition of
                Nothing -> (implicitModules, defaultNames)
                Just baseDefinition -> baseDefinition

    names <- foldM verifyUniqueNames baseNames (definitionModules definition)

    indexedModules <-
        castError $ foldM
            (indexModuleIfNeeded
                implicitModule
                nameToModule
            )
            baseIndexedModules
            (definitionModules definition)
    mapM_ (verifyModule attributesVerification builtinVerifiers) (Map.elems indexedModules)
    verifyAttributes
        (definitionAttributes definition)
        attributesVerification

    return (indexedModules, names)
  where
    nameToModule =
        Map.fromList
            (map (\m -> (moduleName m, m)) (definitionModules definition))

defaultAttributesVerification
    :: ParseAttributes atts
    => Proxy atts
    -> AttributesVerification atts
defaultAttributesVerification = VerifyAttributes

indexImplicitModules
    :: ParseAttributes atts
    => Either
        (Error VerifyError)
        ( Map.Map ModuleName (KoreIndexedModule atts)
        , KoreImplicitIndexedModule atts
        , Map.Map Text AstLocation
        )
indexImplicitModules = do
    defaultNames <- foldM verifyUniqueNames sortNames uncheckedKoreModules
    (indexedModules, defaultModule) <-
        castError $ foldM
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
"Kore.Implicit" package. It verifies the correctness of a definition
containing only the 'kore' default module.
-}
verifyNormalKoreDefinition
    :: ParseAttributes atts
    => AttributesVerification atts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) (KoreIndexedModule atts)
verifyNormalKoreDefinition
    attributesVerification
    builtinVerifiers
    definition
  = do
    -- VerifyDefinition already checks the Kore module, so we skip it.
    modules <-
        verifyAndIndexDefinition
            attributesVerification
            builtinVerifiers
            definition
    name <- extractSingleModuleNameFromDefinition definition
    findModule name modules

{-|'verifyImplicitKoreDefinition' is meant to be used only in the
"Kore.Implicit" package. It verifies the correctness of a definition
containing only the 'kore' default module.
-}
verifyImplicitKoreDefinition
    :: ParseAttributes atts
    => AttributesVerification atts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) (KoreIndexedModule atts)
verifyImplicitKoreDefinition
    attributesVerification
    builtinVerifiers
    definition
  = do
    modules <-
        verifyAndIndexDefinition
            attributesVerification
            builtinVerifiers
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
    -> Map.Map ModuleName (KoreIndexedModule atts)
    -> Either (Error VerifyError) (KoreIndexedModule atts)
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
