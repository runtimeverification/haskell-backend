{- |
Module      : Kore.Validate.DefinitionVerifier
Description : Tools for verifying the wellformedness of a Kore 'Definiton'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Validate.DefinitionVerifier (
    verifyDefinition,
    verifyAndIndexDefinition,
    verifyAndIndexDefinitionWithBase,
    sortModuleClaims,
) where

import Control.Lens (
    (%~),
 )
import Control.Monad (
    foldM,
 )
import Data.Generics.Product (
    field,
 )
import Data.List (
    sortOn,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
import qualified Kore.Internal.Symbol as Internal.Symbol (
    Symbol (..),
 )
import Kore.Syntax.Definition
import Kore.Syntax.Variable
import Kore.Validate.AttributesVerifier hiding (
    parseAttributes,
 )
import Kore.Validate.Error
import Kore.Validate.ModuleVerifier
import Kore.Validate.Verifier
import qualified Kore.Verified as Verified
import Prelude.Kore

{- |'verifyDefinition' verifies the welformedness of a Kore 'Definition'.

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
verifyDefinition ::
    Builtin.Verifiers ->
    ParsedDefinition ->
    Either (Error VerifyError) VerifySuccess
verifyDefinition builtinVerifiers definition = do
    _ <-
        verifyAndIndexDefinition builtinVerifiers definition
    verifySuccess

{- |'verifyAndIndexDefinition' verifies a definition and returns an indexed
collection of the definition's modules.
-}
verifyAndIndexDefinition ::
    Builtin.Verifiers ->
    ParsedDefinition ->
    Either
        (Error VerifyError)
        (Map.Map ModuleName (VerifiedModule Attribute.Symbol.Symbol))
verifyAndIndexDefinition builtinVerifiers definition = do
    (indexedModules, _defaultNames) <-
        verifyAndIndexDefinitionWithBase
            mempty
            builtinVerifiers
            definition
    return indexedModules

{- |Verifies a `ParsedDefinition` against a preverified definition, consisting of
map of indexed modules and a map of defined names.

If verification is successfull, it returns the updated maps of indexed modules
and defined names.
-}
verifyAndIndexDefinitionWithBase ::
    (Map ModuleName VerifiedModule', Map Text AstLocation) ->
    Builtin.Verifiers ->
    ParsedDefinition ->
    Either
        (Error VerifyError)
        (Map ModuleName VerifiedModule', Map Text AstLocation)
verifyAndIndexDefinitionWithBase
    alreadyVerified
    builtinVerifiers
    definition =
        do
            let (verifiedModulesCache, baseNames) =
                    (implicitModules, implicitNames) <> alreadyVerified

            names <- foldM verifyUniqueNames baseNames (definitionModules definition)

            let implicitModule ::
                    ImplicitIndexedModule
                        Verified.Pattern
                        Attribute.Symbol.Symbol
                        (Attribute.Axiom Internal.Symbol.Symbol VariableName)
                implicitModule = ImplicitIndexedModule implicitIndexedModule
                parsedModules = modulesByName (definitionModules definition)
                definitionModuleNames = moduleName <$> definitionModules definition
                verifyModules = traverse_ verifyModule definitionModuleNames

            -- Verify the contents of the definition.
            (_, index) <-
                runVerifier
                    verifyModules
                    verifiedModulesCache
                    implicitModule
                    parsedModules
                    builtinVerifiers
            verifyAttributes (definitionAttributes definition)

            return (index, names)
      where
        modulesByName = Map.fromList . map (\m -> (moduleName m, m))

sortModuleClaims ::
    VerifiedModule declAtts ->
    VerifiedModule declAtts
sortModuleClaims verifiedModule =
    verifiedModule
        & field @"indexedModuleClaims"
            %~ sortOn (Attribute.sourceLocation . fst)
