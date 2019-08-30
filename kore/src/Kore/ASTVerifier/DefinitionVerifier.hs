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
    , AttributesVerification (..)
    ) where

import           Control.Monad
                 ( foldM )
import           Control.Monad.State.Strict
                 ( execStateT )
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Proxy
                 ( Proxy (..) )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.ASTVerifier.AttributesVerifier hiding
                 ( parseAttributes )
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.ModuleVerifier
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Syntax.Definition
import qualified Kore.Verified as Verified

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
    :: ParseAttributes Attribute.Axiom
    => AttributesVerification Attribute.Symbol Attribute.Axiom
    -> Builtin.Verifiers
    -> ParsedDefinition
    -> Either (Error VerifyError) VerifySuccess
verifyDefinition attributesVerification builtinVerifiers definition = do
    _ <-
        verifyAndIndexDefinition
            attributesVerification builtinVerifiers definition
    verifySuccess

{-|'verifyAndIndexDefinition' verifies a definition and returns an indexed
collection of the definition's modules.
-}
verifyAndIndexDefinition
    :: ParseAttributes Attribute.Axiom
    => AttributesVerification Attribute.Symbol Attribute.Axiom
    -> Builtin.Verifiers
    -> ParsedDefinition
    -> Either
        (Error VerifyError)
        (Map.Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
verifyAndIndexDefinition attributesVerification builtinVerifiers definition = do
    (indexedModules, _defaultNames) <-
        verifyAndIndexDefinitionWithBase
            Nothing
            attributesVerification
            builtinVerifiers
            definition
    return indexedModules

{-|Verifies a `ParsedDefinition` against a preverified definition, consisting of
map of indexed modules and a map of defined names.

If verification is successfull, it returns the updated maps op indexed modules
and defined names.
-}
verifyAndIndexDefinitionWithBase
    :: Maybe
        ( Map.Map ModuleName (KoreIndexedModule Attribute.Symbol Attribute.Axiom)
        , Map.Map Text AstLocation
        )
    -> AttributesVerification Attribute.Symbol Attribute.Axiom
    -> Builtin.Verifiers
    -> ParsedDefinition
    -> Either (Error VerifyError)
        ( Map.Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom)
        , Map.Map Text AstLocation
        )
verifyAndIndexDefinitionWithBase
    maybeBaseDefinition
    attributesVerification
    builtinVerifiers
    definition
  = do
    let
        (_, baseNames) =
            fromMaybe (implicitModules, implicitNames) maybeBaseDefinition

    names <- foldM verifyUniqueNames baseNames (definitionModules definition)

    let
        verifiedDefaultModule
            :: ImplicitIndexedModule Verified.Pattern Attribute.Symbol Attribute.Axiom
        verifiedDefaultModule = ImplicitIndexedModule implicitIndexedModule

    -- Verify the contents of the definition.
    index <-
        execStateT
            (traverse
                (verifyModuleByName
                    (Just verifiedDefaultModule)
                    (modulesByName $ definitionModules definition)
                    Set.empty
                    attributesVerification
                    builtinVerifiers
                )
                (moduleName <$> definitionModules definition)
            )
            Map.empty
    verifyAttributes
        (definitionAttributes definition)
        attributesVerification

    return (index, names)
  where
    modulesByName = Map.fromList . map (\m -> (moduleName m, m))

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
