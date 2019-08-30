{-|
Module      : Kore.ASTVerifier.ModuleVerifier
Description : Tools for verifying the wellformedness of a Kore 'Module'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.ModuleVerifier
    ( verifyModuleByName
    , verifyUniqueNames
    ) where

import           Control.Lens
                 ( (%=), (.=) )
import qualified Control.Monad as Monad
import           Control.Monad.State.Strict
                 ( StateT, execStateT )
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import           Data.Function
import           Data.Generics.Product
import qualified Data.List as List
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
import qualified Kore.ASTVerifier.SentenceVerifier as SentenceVerifier
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Hook
                 ( getHookAttribute )
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.Syntax
import           Kore.Syntax.Definition
import           Kore.Unparser
import qualified Kore.Verified as Verified

{-|'verifyUniqueNames' verifies that names defined in a module are unique both
within the module and outside, using the provided name set. -}
verifyUniqueNames
    :: Unparse pat
    => Map.Map Text AstLocation
    -- ^ Names that are already defined.
    -> Module (Sentence pat)
    -> Either (Error VerifyError) (Map.Map Text AstLocation)
    -- ^ On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
verifyUniqueNames existingNames koreModule =
    withContext
        ("module '" ++ getModuleNameForError (moduleName koreModule) ++ "'")
        (SentenceVerifier.verifyUniqueNames
            (moduleSentences koreModule)
            existingNames
        )

verifyModuleByName
    ::  Maybe (ImplicitIndexedModule Verified.Pattern Attribute.Symbol Attribute.Axiom)
            -- TODO: Move ImplicitIndexedModule into a reader field.
    ->  Map ModuleName (Module ParsedSentence)
            -- TODO: Move this Map into a reader field.
    ->  Set ModuleName
            -- TODO: Move this Set into a reader field.
    ->  AttributesVerification Attribute.Symbol Attribute.Axiom
            -- TODO: Move AttributesVerification into a reader field.
    ->  Builtin.Verifiers
            -- TODO: Move BuiltinVerifiers into a reader field.
    ->  ModuleName
    ->  StateT
            (Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
            (Either (Error VerifyError))
            (VerifiedModule Attribute.Symbol Attribute.Axiom)
verifyModuleByName
    implicitModule
    modules
    importing
    attributesVerification
    builtinVerifiers
    name
  =
    withContext moduleContext $ do
        checkImportCycle
        indexed <- State.get
        Map.lookup name indexed & maybe notYetIndexed alreadyIndexed
  where
    moduleContext = "module '" ++ getModuleNameForError name ++ "'"
    importing' = Set.insert name importing'
    checkImportCycle =
        koreFailWhen
            (Set.member name importing)
            "Circular module import dependency."
    notFound = koreFail "Module not found."
    alreadyIndexed = return
    notYetIndexed = do
        module' <- Map.lookup name modules & maybe notFound return
        let Module { moduleAttributes } = module'
        attrs <- parseAttributes' moduleAttributes
        let indexedModule0 = indexedModuleWithDefaultImports name implicitModule
            Module { moduleSentences } = module'
            sentences = List.sort moduleSentences
        indexedModule1 <-
            flip execStateT indexedModule0 $ do
                field @"indexedModuleAttributes" .= (attrs, moduleAttributes)
                Foldable.traverse_
                    (indexSentenceImport implicitModule modules importing' attributesVerification builtinVerifiers)
                    sentences
                Foldable.traverse_
                    (indexSentenceSort attributesVerification builtinVerifiers)
                    sentences
                Foldable.traverse_
                    (indexSentenceSymbol attributesVerification builtinVerifiers)
                    sentences
                -- TODO: indexSentenceAlias
                -- TODO: indexSentenceAxiom
                -- TODO: indexSentenceClaim
                -- TODO: The corresponding functions in
                -- Kore.IndexedModule.IndexedModule can go away.
        _ <- internalIndexedModuleSubsorts indexedModule1
        State.modify (Map.insert name indexedModule1)
        return indexedModule1

indexSentenceImport
    ::  Maybe (ImplicitIndexedModule Verified.Pattern Attribute.Symbol Attribute.Axiom)
    ->  Map ModuleName (Module ParsedSentence)
    ->  Set ModuleName
    ->  AttributesVerification Attribute.Symbol Attribute.Axiom
    ->  Builtin.Verifiers
    ->  Sentence ParsedPattern
    ->  StateT (VerifiedModule Attribute.Symbol Attribute.Axiom)
            (StateT (Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
                (Either (Error VerifyError)))
            ()
indexSentenceImport
    implicitModule
    modules
    importing
    attributesVerification
    builtinVerifiers
  =
    \case
        SentenceImportSentence sentence -> worker sentence
        _ -> return ()
  where
    worker sentence = do
        _ <- parseAttributes' @Attribute.Symbol (sentenceImportAttributes sentence)
        let name = sentenceImportModuleName sentence
        _ <- Trans.lift $ verifyModuleByName implicitModule modules importing attributesVerification builtinVerifiers name
        return ()

parseAttributes'
    :: forall attrs error e
    .  (MonadError (Error e) error, ParseAttributes attrs)
    => Attributes
    -> error attrs
parseAttributes' =
    Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

indexSentenceSort
    ::  AttributesVerification Attribute.Symbol Attribute.Axiom
    ->  Builtin.Verifiers
    ->  Sentence ParsedPattern
    ->  StateT (VerifiedModule Attribute.Symbol Attribute.Axiom)
            (StateT (Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
                (Either (Error VerifyError)))
            ()
indexSentenceSort
    attributesVerification
    builtinVerifiers
  =
    \case
        SentenceSortSentence sentence ->
            worker False sentence
        SentenceHookSentence (SentenceHookedSort sentence) ->
            worker True sentence
        _ -> return ()
  where
    worker isHooked sentence = do
        verified <-
            liftSentenceVerifier
                (SentenceVerifier.verifySortSentence sentence)
                attributesVerification
                builtinVerifiers
        let name = sentenceSortName sentence
            attrs0 = sentenceSortAttributes verified
        attrs1 <- parseAttributes' attrs0
        field @"indexedModuleSortDescriptions"
            %= Map.insert name (attrs1, verified)
        Monad.when isHooked $ do
            field @"indexedModuleHookedIdentifiers" %= Set.insert name
            hook <- getHookAttribute attrs0
            field @"indexedModuleHooks"
                %= Map.alter (Just . maybe [name] (name :)) hook

indexSentenceSymbol
    ::  AttributesVerification Attribute.Symbol Attribute.Axiom
    ->  Builtin.Verifiers
    ->  Sentence ParsedPattern
    ->  StateT (VerifiedModule Attribute.Symbol Attribute.Axiom)
            (StateT (Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
                (Either (Error VerifyError)))
            ()
indexSentenceSymbol
    attributesVerification
    builtinVerifiers
  =
    \case
        SentenceSymbolSentence sentence ->
            worker False sentence
        SentenceHookSentence (SentenceHookedSymbol sentence) ->
            worker True sentence
        _ -> return ()
  where
    worker isHooked sentence = do
        verified <-
            liftSentenceVerifier
                (SentenceVerifier.verifySymbolSentence sentence)
                attributesVerification
                builtinVerifiers
        let Symbol { symbolConstructor = name } = sentenceSymbolSymbol sentence
            attrs0 = sentenceSymbolAttributes sentence
        attrs1 <- parseAttributes' attrs0
        field @"indexedModuleSymbolSentences"
            %= Map.insert name (attrs1, verified)
        Monad.when isHooked $ do
            field @"indexedModuleHookedIdentifiers" %= Set.insert name
            hook <- getHookAttribute attrs0
            field @"indexedModuleHooks"
                %= Map.alter (Just . maybe [name] (name :)) hook

liftSentenceVerifier
    ::  SentenceVerifier.SentenceVerifier a
    ->  AttributesVerification Attribute.Symbol Attribute.Axiom
    ->  Builtin.Verifiers
    ->  StateT (VerifiedModule Attribute.Symbol Attribute.Axiom)
            (StateT (Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
                (Either (Error VerifyError)))
            a
liftSentenceVerifier
    sentenceVerifier
    attributesVerification
    builtinVerifiers
  = do
    verifiedModule <- State.get
    Trans.lift . Trans.lift
        $ SentenceVerifier.runSentenceVerifier
            sentenceVerifier
            verifiedModule
            attributesVerification
            builtinVerifiers
