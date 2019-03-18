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
    , defaultNullAttributesVerification
    , verifyDefinition
    , verifyAndIndexDefinition
    , verifyAndIndexDefinitionWithBase
    , verifyImplicitKoreDefinition
    , verifyNormalKoreDefinition
    , AttributesVerification (..)
    ) where

import           Control.Monad
                 ( foldM )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Kore
import qualified Kore.AST.Pure as AST.Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.ModuleVerifier
import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.Implicit.ImplicitKore
                 ( uncheckedKoreModule )
import           Kore.Implicit.ImplicitSorts
                 ( predicateSortActual )
import           Kore.IndexedModule.IndexedModule
import           Kore.Unparser

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
    :: (ParseAttributes declAtts, ParseAttributes axiomAtts)
    => AttributesVerification declAtts axiomAtts
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
    :: (ParseAttributes declAtts, ParseAttributes axiomAtts)
    => AttributesVerification declAtts axiomAtts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) (Map.Map ModuleName (VerifiedModule declAtts axiomAtts))
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
    :: forall declAtts axiomAtts
    .  (ParseAttributes declAtts, ParseAttributes axiomAtts)
    => Maybe
        ( Map.Map ModuleName (VerifiedModule declAtts axiomAtts)
        , Map.Map Text AstLocation
        )
    -> AttributesVerification declAtts axiomAtts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError)
        ( Map.Map ModuleName (VerifiedModule declAtts axiomAtts)
        , Map.Map Text AstLocation
        )
verifyAndIndexDefinitionWithBase
    maybeBaseDefinition
    attributesVerification
    builtinVerifiers
    definition
  = do
    (implicitModules, implicitDefaultModule, defaultNames) <-
        withContext "Indexing unverified implicit Kore modules"
        $ indexImplicitModule
        $ modulePureToKore $ castModuleDomainValues
        $ eraseSentenceAnnotations <$> uncheckedKoreModule
    let
        (baseIndexedModules, baseNames) =
            case maybeBaseDefinition of
                Nothing -> (implicitModules, defaultNames)
                Just (baseIndexedModules', baseNames') ->
                    ( (<$>)
                        (mapIndexedModulePatterns eraseAnnotations)
                        baseIndexedModules'
                    , baseNames'
                    )

    names <- foldM verifyUniqueNames baseNames (definitionModules definition)

    let
        ImplicitIndexedModule defaultModule = implicitDefaultModule
        indexModules
            :: [KoreModule]
            -> Either
                (Error VerifyError)
                (Map.Map ModuleName (KoreIndexedModule declAtts axiomAtts))
        indexModules modules =
            castError $ foldM
                (indexModuleIfNeeded
                    (Just implicitDefaultModule)
                    unverifiedModulesByName
                )
                baseIndexedModules
                modules
          where
            unverifiedModulesByName =
                modulesByName modules

        verifyModule' = verifyModule attributesVerification builtinVerifiers
        verifyModules = traverse verifyModule'

    -- Verify and index the implicit modules
    (verifiedImplicitModules, verifiedDefaultModule, _) <-
        withContext "Indexing verified implicit Kore modules"
        $ indexImplicitModule =<< verifyModule' defaultModule

    -- Index the unverified modules.
    indexedModules <- indexModules (definitionModules definition)

    -- Verify the contents of the definition.
    verifiedModules <- verifyModules (Map.elems indexedModules)
    verifyAttributes
        (definitionAttributes definition)
        attributesVerification

    let
        indexVerifiedModules
            :: [Module VerifiedKoreSentence]
            -> Either
                (Error VerifyError)
                (Map.Map ModuleName (VerifiedModule declAtts axiomAtts))
        indexVerifiedModules modules =
            castError $ foldM
                (indexModuleIfNeeded
                    (Just verifiedDefaultModule)
                    verifiedModulesByName
                )
                verifiedImplicitModules
                modules
          where
            verifiedModulesByName = modulesByName modules

    -- Re-index the (now verified) modules.
    reindexedModules <- indexVerifiedModules verifiedModules
    return (reindexedModules, names)
  where
    modulesByName = Map.fromList . map (\m -> (moduleName m, m))
    castModuleDomainValues = (fmap . fmap) AST.Pure.castVoidDomainValues

defaultAttributesVerification
    :: (ParseAttributes declAtts, ParseAttributes axiomAtts)
    => Proxy declAtts
    -> Proxy axiomAtts
    -> AttributesVerification declAtts axiomAtts
defaultAttributesVerification = VerifyAttributes

-- |default option for verifying attributes without parsing them
defaultNullAttributesVerification
    :: AttributesVerification Attribute.Null Attribute.Null
defaultNullAttributesVerification =
   defaultAttributesVerification proxy proxy
  where
    proxy :: Proxy Attribute.Null
    proxy = Proxy

indexImplicitModule
    :: (Unparse sortParam, Unparse patternType, ParseAttributes declAtts, ParseAttributes axAtts)
    => Module (UnifiedSentence sortParam patternType)
    -> Either
        (Error VerifyError)
        ( Map ModuleName (IndexedModule sortParam patternType declAtts axAtts)
        , ImplicitIndexedModule sortParam patternType declAtts axAtts
        , Map Text AstLocation
        )
indexImplicitModule implicitModule = do
    defaultNames <- verifyUniqueNames preImplicitNames implicitModule
    indexedModules <-
        castError $ indexModuleIfNeeded
            Nothing
            modulesByName
            Map.empty
            implicitModule
    defaultModule <- lookupDefaultModule indexedModules
    return (indexedModules, ImplicitIndexedModule defaultModule, defaultNames)
  where
    -- Names which are hard-coded into Kore that do not even appear in the
    -- implicit definition.
    preImplicitNames =
        Map.fromList ((,) <$> names <*> pure AstLocationImplicit)
      where
        names =
            [ Text.pack (show StringSort)
            -- Reserved for internal use.
            -- See TODO PREDICATE in Kore.ASTUtils.SmartConstructors
            , getId (sortActualName predicateSortActual)
            ]
    implicitModuleName = moduleName implicitModule
    moduleNameForError = getModuleNameForError implicitModuleName
    modulesByName = Map.singleton implicitModuleName implicitModule
    lookupDefaultModule indexedModules =
        case Map.lookup (moduleName implicitModule) indexedModules of
            Just defaultModule -> return defaultModule
            Nothing ->
                koreFail
                    ("Missing default module '" ++ moduleNameForError ++ "'.")

{-|'verifyNormalKoreDefinition' is meant to be used only in the
"Kore.Implicit" package. It verifies the correctness of a definition
containing only the 'kore' default module.
-}
verifyNormalKoreDefinition
    ::  ( ParseAttributes declAtts
        , Show declAtts
        , ParseAttributes axiomAtts
        , Show axiomAtts
        )
    => AttributesVerification declAtts axiomAtts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) (VerifiedModule declAtts axiomAtts)
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
    :: (ParseAttributes declAtts, ParseAttributes axiomAtts)
    => AttributesVerification declAtts axiomAtts
    -> Builtin.Verifiers
    -> KoreDefinition
    -> Either (Error VerifyError) (VerifiedModule declAtts axiomAtts)
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
    -> Map.Map ModuleName (IndexedModule param pat declAtts axiomAtts)
    -> Either (Error VerifyError) (IndexedModule param pat declAtts axiomAtts)
findModule name modules =
    case Map.lookup name modules of
        Just a -> return a
        Nothing ->
            koreFail
                (  "Internal error: the kore module ("
                ++ getModuleNameForError name
                ++ ") was not indexed ("
                ++ show (Map.keys modules)
                ++ ")."
                )
