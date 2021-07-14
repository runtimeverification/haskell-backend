{- |
Module      : Kore.Validate.ModuleVerifier
Description : Tools for verifying the wellformedness of a Kore 'Module'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Validate.ModuleVerifier (
    verifyModule,
    verifyUniqueNames,
) where

import Control.Lens (
    (%=),
 )
import qualified Control.Lens as Lens
import qualified Control.Monad.Reader.Class as Reader
import qualified Control.Monad.State.Class as State
import Data.Generics.Product
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import Kore.AST.Error
import Kore.Attribute.Parser (
    ParseAttributes,
 )
import qualified Kore.Attribute.Parser as Attribute.Parser
import Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Validate.AliasVerifier
import Kore.Validate.Error
import Kore.Validate.SentenceVerifier (
    SentenceVerifier,
    verifyAxioms,
    verifyClaims,
    verifyHookedSorts,
    verifyHookedSymbols,
    verifyNonHooks,
    verifySorts,
    verifySymbols,
 )
import qualified Kore.Validate.SentenceVerifier as SentenceVerifier
import Kore.Validate.Verifier
import Prelude.Kore

{- |'verifyUniqueNames' verifies that names defined in a module are unique both
within the module and outside, using the provided name set.
-}
verifyUniqueNames ::
    -- | Names that are already defined.
    Map.Map Text AstLocation ->
    Module (Sentence pat) ->
    -- | On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
    Either (Error VerifyError) (Map.Map Text AstLocation)
verifyUniqueNames existingNames koreModule =
    withContext
        ("module '" ++ getModuleNameForError (moduleName koreModule) ++ "'")
        ( SentenceVerifier.verifyUniqueNames
            (moduleSentences koreModule)
            existingNames
        )

{- | Verify the named module.

The cached 'VerifiedModule' is returned if available; otherwise the module is
verified and cached.

See also: 'verifyUncachedModule'
-}
verifyModule :: ModuleName -> Verifier VerifiedModule'
verifyModule name = lookupVerifiedModule name >>= maybe notCached cached
  where
    cached = return
    notCached = verifyUncachedModule name

-- | Verify the named module, irrespective of the cache.
verifyUncachedModule :: ModuleName -> Verifier VerifiedModule'
verifyUncachedModule name = whileImporting name $ do
    module' <- lookupParsedModule name
    let Module{moduleSentences} = module'
        sentences = List.sort moduleSentences
    (_, indexedModule) <-
        withModuleContext name (newVerifiedModule module')
            >>= SentenceVerifier.runSentenceVerifier
                ( do
                    verifyImports sentences
                    withModuleContext name $ do
                        verifySorts sentences
                        verifySymbols sentences
                        verifyHookedSorts sentences
                        verifyHookedSymbols sentences
                        verifyNonHooks sentences
                        verifyAliases sentences
                        verifyAxioms sentences
                        verifyClaims sentences
                )
    _ <-
        withModuleContext name $
            internalIndexedModuleSubsorts indexedModule
    field @"verifiedModules" %= Map.insert name indexedModule
    return indexedModule

{- | Construct a new 'VerifiedModule' for the 'ParsedModule'.

The new 'VerifiedModule' is empty except for its 'ModuleName', its 'Attributes',
and the 'ImplicitModule' import.
-}
newVerifiedModule :: ParsedModule -> Verifier VerifiedModule'
newVerifiedModule module' = do
    VerifierContext{implicitModule} <- Reader.ask
    let Module{moduleName, moduleAttributes} = module'
    attrs <- parseAttributes' moduleAttributes
    return
        ( indexedModuleWithDefaultImports moduleName (Just implicitModule)
            & Lens.set (field @"indexedModuleAttributes") (attrs, moduleAttributes)
        )

{- | Project the 'SentenceImport's out the list and verify them.

The named modules are verified and imported into the current 'VerifiedModule'.
-}
verifyImports :: [ParsedSentence] -> SentenceVerifier ()
verifyImports = traverse_ verifyImport . mapMaybe projectSentenceImport

verifyImport :: SentenceImport -> SentenceVerifier ()
verifyImport sentence =
    withSentenceImportContext sentence $ do
        let SentenceImport{sentenceImportAttributes = attrs0} = sentence
        attrs1 <- parseAttributes' attrs0
        let importName = sentenceImportModuleName sentence
        verified <- lift $ verifyModule importName
        State.modify' $ addImport verified attrs1 attrs0
  where
    addImport verified attrs1 attrs0 =
        Lens.over
            (field @"indexedModuleImports")
            ((attrs1, attrs0, verified) :)

parseAttributes' ::
    forall attrs error e.
    (MonadError (Error e) error, ParseAttributes attrs) =>
    Attributes ->
    error attrs
parseAttributes' =
    Attribute.Parser.liftParser . Attribute.Parser.parseAttributes
