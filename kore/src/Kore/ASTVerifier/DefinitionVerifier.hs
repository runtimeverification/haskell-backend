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
  ( defaultAttributesVerification,
    defaultNullAttributesVerification,
    verifyDefinition,
    verifyAndIndexDefinition,
    verifyAndIndexDefinitionWithBase,
    AttributesVerification (..)
    )
where

import Control.Monad
  ( foldM
    )
import qualified Data.Map as Map
import Data.Maybe
import Data.Proxy
  ( Proxy (..)
    )
import Data.Text
  ( Text
    )
import Kore.ASTVerifier.AttributesVerifier
import Kore.ASTVerifier.Error
import Kore.ASTVerifier.ModuleVerifier
import qualified Kore.Attribute.Null as Attribute
import Kore.Attribute.Parser
  ( ParseAttributes (..)
    )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Syntax as Syntax
import Kore.Syntax.Definition
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
  :: ParseAttributes axiomAtts
  => AttributesVerification Attribute.Symbol axiomAtts
  -> Builtin.Verifiers
  -> ParsedDefinition
  -> Either (Error VerifyError) VerifySuccess
verifyDefinition attributesVerification builtinVerifiers definition = do
  _ <-
    verifyAndIndexDefinition
      attributesVerification
      builtinVerifiers
      definition
  verifySuccess

{-|'verifyAndIndexDefinition' verifies a definition and returns an indexed
collection of the definition's modules.
-}
verifyAndIndexDefinition
  :: ParseAttributes axiomAtts
  => AttributesVerification Attribute.Symbol axiomAtts
  -> Builtin.Verifiers
  -> ParsedDefinition
  -> Either
       (Error VerifyError)
       (Map.Map ModuleName (VerifiedModule Attribute.Symbol axiomAtts))
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
  :: forall axiomAtts. ParseAttributes axiomAtts
  => Maybe
       ( Map.Map ModuleName (KoreIndexedModule Attribute.Symbol axiomAtts),
         Map.Map Text AstLocation
         )
  -> AttributesVerification Attribute.Symbol axiomAtts
  -> Builtin.Verifiers
  -> ParsedDefinition
  -> Either (Error VerifyError)
       ( Map.Map ModuleName (VerifiedModule Attribute.Symbol axiomAtts),
         Map.Map Text AstLocation
         )
verifyAndIndexDefinitionWithBase
  maybeBaseDefinition
  attributesVerification
  builtinVerifiers
  definition =
    do
      let (baseIndexedModules, baseNames) =
            fromMaybe (implicitModules, implicitNames) maybeBaseDefinition
      names <- foldM verifyUniqueNames baseNames (definitionModules definition)
      let defaultModule
            :: ImplicitIndexedModule ParsedPattern Attribute.Symbol axiomAtts
          defaultModule = ImplicitIndexedModule implicitIndexedModule
          indexModules
            :: [ParsedModule]
            -> Either
                 (Error VerifyError)
                 (Map.Map ModuleName (KoreIndexedModule Attribute.Symbol axiomAtts))
          indexModules modules =
            castError
              $ foldM
                  ( indexModuleIfNeeded
                      (Just defaultModule)
                      (modulesByName modules)
                    )
                  baseIndexedModules
                  modules
          verifyModule' = verifyModule attributesVerification builtinVerifiers
          verifyModules = traverse verifyModule'
      -- Index the unverified modules.
      indexedModules <- indexModules (definitionModules definition)
      -- Verify the contents of the definition.
      verifiedModules <- verifyModules (Map.elems indexedModules)
      verifyAttributes
        (definitionAttributes definition)
        attributesVerification
      let verifiedDefaultModule
            :: ImplicitIndexedModule Verified.Pattern Attribute.Symbol axiomAtts
          verifiedDefaultModule = ImplicitIndexedModule implicitIndexedModule
          indexVerifiedModules
            :: [Module Verified.Sentence]
            -> Either
                 (Error VerifyError)
                 (Map.Map ModuleName (VerifiedModule Attribute.Symbol axiomAtts))
          indexVerifiedModules modules =
            castError
              $ foldM
                  ( indexModuleIfNeeded
                      (Just verifiedDefaultModule)
                      verifiedModulesByName
                    )
                  implicitModules
                  modules
            where
              verifiedModulesByName = modulesByName modules
      -- Re-index the (now verified) modules.
      reindexedModules <- indexVerifiedModules verifiedModules
      return (reindexedModules, names)
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
