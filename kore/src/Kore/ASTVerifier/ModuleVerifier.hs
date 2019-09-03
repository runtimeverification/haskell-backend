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
    ( verifyModule
    , verifyUniqueNames
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Lens
                 ( (%=) )
import qualified Control.Lens as Lens
import qualified Control.Monad.Reader.Class as Reader
import qualified Control.Monad.State.Class as State
import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import           Data.Function
import           Data.Generics.Product
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Error
import           Kore.ASTVerifier.AliasVerifier
import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.SentenceVerifier
                 ( SentenceVerifier, verifySortSentences )
import qualified Kore.ASTVerifier.SentenceVerifier as SentenceVerifier
import           Kore.ASTVerifier.Verifier
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.Error
import           Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Syntax
import           Kore.Syntax.Definition
import           Kore.Unparser

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

verifyModule :: ModuleName -> Verifier VerifiedModule'
verifyModule name = lookupVerifiedModule name >>= maybe notCached cached
  where
    cached = return
    notCached = verifyUncachedModule name

verifyUncachedModule :: ModuleName -> Verifier VerifiedModule'
verifyUncachedModule name = whileImporting name $ do
    module' <- lookupParsedModule name
    let Module { moduleSentences } = module'
        sentences = List.sort moduleSentences
    (_, indexedModule) <-
            withModuleContext name (newVerifiedModule module')
        >>= SentenceVerifier.runSentenceVerifier
            (do
                verifyImports sentences
                withModuleContext name $ do
                    -- TODO: The corresponding functions in
                    -- Kore.IndexedModule.IndexedModule can go away.
                    verifySortSentences  sentences
                    verifySymbols        sentences
                    verifyHookedSorts    sentences
                    verifyHookedSymbols  sentences
                    verifyNonHooks       sentences
                    verifyAliases        sentences
                    verifyAxioms         sentences
                    verifyClaims         sentences
            )
    _ <-
        withModuleContext name
        $ internalIndexedModuleSubsorts indexedModule
    field @"verifiedModules" %= Map.insert name indexedModule
    return indexedModule

newVerifiedModule :: Module ParsedSentence -> Verifier VerifiedModule'
newVerifiedModule module' = do
    VerifierContext { implicitModule } <- Reader.ask
    let Module { moduleName, moduleAttributes } = module'
    attrs <- parseAttributes' moduleAttributes
    return
        ( indexedModuleWithDefaultImports moduleName implicitModule
        & Lens.set (field @"indexedModuleAttributes") (attrs, moduleAttributes)
        )

verifyImports :: [ParsedSentence] -> SentenceVerifier ()
verifyImports = Foldable.traverse_ verifyImport . mapMaybe projectSentenceImport

verifyImport :: SentenceImport ParsedPattern -> SentenceVerifier ()
verifyImport sentence =
    withSentenceImportContext sentence $ do
        let SentenceImport { sentenceImportAttributes = attrs0 } = sentence
        attrs1 <- parseAttributes' attrs0
        let importName = sentenceImportModuleName sentence
        verified <- Trans.lift $ verifyModule importName
        State.modify' $ addImport verified attrs1 attrs0
  where
    addImport verified attrs1 attrs0 =
        Lens.over
            (field @"indexedModuleImports")
            ((attrs1, attrs0, verified) :)

parseAttributes'
    :: forall attrs error e
    .  (MonadError (Error e) error, ParseAttributes attrs)
    => Attributes
    -> error attrs
parseAttributes' =
    Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

addIndexedModuleHook
    :: Id
    -> Attribute.Hook
    -> VerifiedModule'
    -> VerifiedModule'
addIndexedModuleHook name hook =
    Lens.over (field @"indexedModuleHookedIdentifiers") (Set.insert name)
    . Lens.over (field @"indexedModuleHooks") addHook
  where
    addHook
      | Just hookId <- Attribute.getHook hook =
        Map.alter (Just . maybe [name] (name :)) hookId
      | otherwise           = id

verifyHookedSorts :: [ParsedSentence] -> SentenceVerifier ()
verifyHookedSorts =
    Foldable.traverse_ verifyHookedSort . mapMaybe projectSentenceHookedSort

{- | Find the attributes for the named sort.

It is an error to use this before 'verifySorts'.

 -}
lookupSortAttributesHere :: Id -> VerifiedModule' -> Attribute.Sort
lookupSortAttributesHere name verifiedModule =
    Map.lookup name (indexedModuleSortDescriptions verifiedModule)
    & maybe (error $ noSort name) fst

verifyHookedSort :: SentenceSort ParsedPattern -> SentenceVerifier ()
verifyHookedSort sentence =
    withSentenceHookContext (SentenceHookedSort sentence) $ do
        let SentenceSort { sentenceSortAttributes } = sentence
        VerifierContext { attributesVerification } <- Reader.ask
        hook <-
            verifySortHookAttribute
                attributesVerification
                sentenceSortAttributes
        let SentenceSort { sentenceSortName = name } = sentence
        verifiedModule <- State.get
        let attrs = lookupSortAttributesHere name verifiedModule
        VerifierContext { builtinVerifiers } <- Reader.ask
        Builtin.sortDeclVerifier
            builtinVerifiers
            hook
            (IndexedModule.eraseAttributes verifiedModule)
            sentence
            attrs
            & either throwError return
        State.modify' $ addIndexedModuleHook name hook

verifySymbols :: [ParsedSentence] -> SentenceVerifier ()
verifySymbols = Foldable.traverse_ verifySymbol . mapMaybe project
  where
    project sentence =
        projectSentenceSymbol sentence <|> projectSentenceHookedSymbol sentence

verifySymbol :: SentenceSymbol ParsedPattern -> SentenceVerifier ()
verifySymbol sentence =
    withSentenceSymbolContext sentence $ do
        verified <- SentenceVerifier.verifySymbolSentence sentence
        attrs <- parseAttributes' $ sentenceSymbolAttributes sentence
        State.modify' $ addSymbol verified attrs
  where
    addSymbol verified attrs =
        Lens.over
            (field @"indexedModuleSymbolSentences")
            (Map.insert name (attrs, verified))
      where
        Symbol { symbolConstructor = name } = sentenceSymbolSymbol verified

verifyHookedSymbols
    :: [ParsedSentence]
    -> SentenceVerifier ()
verifyHookedSymbols =
    Foldable.traverse_ verifyHookedSymbol . mapMaybe projectSentenceHookedSymbol

verifyHookedSymbol
    :: SentenceSymbol ParsedPattern
    -> SentenceVerifier ()
verifyHookedSymbol sentence =
    withSentenceHookContext (SentenceHookedSymbol sentence) $ do
        let SentenceSymbol { sentenceSymbolAttributes } = sentence
        VerifierContext { attributesVerification } <- Reader.ask
        hook <-
            verifySymbolHookAttribute
                attributesVerification
                sentenceSymbolAttributes
        VerifierContext { builtinVerifiers } <- Reader.ask
        verifiedModule <- State.get
        Builtin.runSymbolVerifier
            (Builtin.symbolVerifier builtinVerifiers hook)
            (findIndexedSort verifiedModule)
            sentence
            & either throwError return
        let Symbol { symbolConstructor = name } = sentenceSymbolSymbol sentence
        State.modify' $ addIndexedModuleHook name hook

verifyAxioms :: [ParsedSentence] -> SentenceVerifier ()
verifyAxioms = Foldable.traverse_ verifyAxiom . mapMaybe projectSentenceAxiom

verifyAxiom :: SentenceAxiom ParsedPattern -> SentenceVerifier ()
verifyAxiom sentence =
    withSentenceAxiomContext sentence $ do
        verified <- SentenceVerifier.verifyAxiomSentence sentence
        attrs <- parseAttributes' $ sentenceAxiomAttributes sentence
        State.modify $ addAxiom verified attrs
  where
    addAxiom verified attrs =
        Lens.over
            (field @"indexedModuleAxioms")
            ((attrs, verified) :)

verifyClaims
    :: [ParsedSentence]
    -> SentenceVerifier ()
verifyClaims = Foldable.traverse_ verifyClaim . mapMaybe projectSentenceClaim

verifyClaim :: SentenceClaim ParsedPattern -> SentenceVerifier ()
verifyClaim sentence =
    withSentenceClaimContext sentence $ do
        verified <- SentenceVerifier.verifyClaimSentence sentence
        attrs <- parseAttributes' $ sentenceClaimAttributes sentence
        State.modify' $ addClaim verified attrs
  where
    addClaim verified attrs =
        Lens.over
            (field @"indexedModuleClaims")
            ((attrs, verified) :)

verifyNonHooks
    :: [ParsedSentence]
    -> SentenceVerifier ()
verifyNonHooks sentences=
    Foldable.traverse_ verifyNonHook nonHookSentences
  where
    nonHookSentences = mapMaybe project sentences
    project (SentenceHookSentence _) = Nothing
    project sentence = Just sentence

verifyNonHook :: ParsedSentence -> SentenceVerifier ()
verifyNonHook sentence =
    withSentenceContext sentence $ do
        VerifierContext { attributesVerification } <- Reader.ask
        verifyNoHookAttribute attributesVerification
            $ sentenceAttributes sentence
