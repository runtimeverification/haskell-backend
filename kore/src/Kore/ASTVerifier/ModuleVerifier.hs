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
import qualified Control.Monad as Monad
import           Control.Monad.Reader
                 ( ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import           Data.Function
import qualified Data.Functor.Foldable as Recursive
import           Data.Generics.Product
import qualified Data.List as List
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified GHC.Generics as GHC

import           Kore.AST.Error
import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
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
import qualified Kore.Verified as Verified

newIndexedModule :: Module ParsedSentence -> Verifier VerifiedModule'
newIndexedModule module' = do
    VerifierContext { implicitModule } <- Reader.ask
    let Module { moduleName, moduleAttributes } = module'
    attrs <- parseAttributes' moduleAttributes
    return
        ( indexedModuleWithDefaultImports moduleName implicitModule
        & Lens.set (field @"indexedModuleAttributes") (attrs, moduleAttributes)
        )

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
    indexedModule <-
        -- TODO: Refactor this in a type-safe way.
            withModuleContext name (newIndexedModule module')
        -- TODO: The corresponding functions in
        -- Kore.IndexedModule.IndexedModule can go away.
        >>= verifyImports        sentences
        >>= withModuleContext name . verifySorts          sentences
        >>= withModuleContext name . verifySymbols        sentences
        >>= withModuleContext name . verifyHookedSorts    sentences
        >>= withModuleContext name . verifyHookedSymbols  sentences
        >>= withModuleContext name . verifyNonHooks       sentences
        >>= withModuleContext name . verifyAliases        sentences
        >>= withModuleContext name . verifyAxioms         sentences
        >>= withModuleContext name . verifyClaims         sentences
    _ <-
        withModuleContext name
        $ internalIndexedModuleSubsorts indexedModule
    field @"verifiedModules" %= Map.insert name indexedModule
    return indexedModule

verifyImports
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyImports sentences verifiedModule =
    Monad.foldM verifyImport verifiedModule
    $ mapMaybe projectSentenceImport sentences

verifyImport
    :: VerifiedModule'
    -> SentenceImport ParsedPattern
    -> Verifier VerifiedModule'
verifyImport verifiedModule sentence =
    withSentenceImportContext sentence $ do
        let SentenceImport { sentenceImportAttributes = attrs0 } = sentence
        attrs1 <- parseAttributes' attrs0
        verified <- verifyModule $ sentenceImportModuleName sentence
        return $ addImport verified attrs1 attrs0 verifiedModule
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

verifySorts
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifySorts sentences verifiedModule =
    Monad.foldM verifySort verifiedModule
    $ mapMaybe project sentences
  where
    project sentence =
        projectSentenceSort sentence <|> projectSentenceHookedSort sentence

verifySort
    :: VerifiedModule'
    -> SentenceSort ParsedPattern
    -> Verifier VerifiedModule'
verifySort verifiedModule sentence =
    withSentenceSortContext sentence $ do
        verified <-
            SentenceVerifier.verifySortSentence sentence
            & SentenceVerifier.liftSentenceVerifier verifiedModule
        attrs <- parseAttributes' $ sentenceSortAttributes verified
        return $ addSort verified attrs verifiedModule
  where
    addSort verified attrs =
        Lens.over
            (field @"indexedModuleSortDescriptions")
            (Map.insert (sentenceSortName verified) (attrs, verified))

verifyAliases
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyAliases sentences verifiedModule = do
    let aliases =
            Map.fromList . map (\sentence -> (aliasName sentence, sentence))
            $ mapMaybe projectSentenceAlias sentences
        aliasIds = Map.keysSet aliases
    runReaderT
        (Monad.foldM verifyAlias verifiedModule aliasIds)
        AliasContext { aliases, verifying = Set.empty }

aliasName :: SentenceAlias patternType -> Id
aliasName = aliasConstructor . sentenceAliasAlias

type AliasVerifierT = ReaderT AliasContext

data AliasContext =
    AliasContext
        { aliases   :: !(Map Id ParsedSentenceAlias)
        , verifying :: !(Set Id)
        }
    deriving (GHC.Generic)

type VerifiedAlias = (Attribute.Symbol, SentenceAlias Verified.Pattern)

lookupVerifiedAlias
    :: Id
    -> VerifiedModule'
    -> AliasVerifierT Verifier (Maybe VerifiedAlias)
lookupVerifiedAlias name verifiedModule =
    return $ Map.lookup name $ indexedModuleAliasSentences verifiedModule

lookupParsedAlias
    :: MonadError (Error e) monad
    => Id
    -> AliasVerifierT monad ParsedSentenceAlias
lookupParsedAlias name =
    Reader.asks (Map.lookup name . aliases) >>= maybe notFound return
  where
    notFound = koreFail "Alias not found."

verifyAlias
    :: VerifiedModule'
    -> Id
    -> AliasVerifierT Verifier VerifiedModule'
verifyAlias verifiedModule name =
    withLocationAndContext name aliasContext $ do
        checkAliasCycle
        lookupVerifiedAlias name verifiedModule
            >>= maybe notYetVerified alreadyVerified
  where
    aliasContext = "alias '" <> getId name <> "' declaration"
    alreadyVerified _ = return verifiedModule
    checkAliasCycle = do
        isCycle <- Reader.asks (Set.member name . verifying)
        koreFailWhen isCycle "Circular alias dependency."
    notYetVerified = do
        sentence <- lookupParsedAlias name
        verifiedModule' <- verifyAliasDependencies verifiedModule sentence
        verified <-
            SentenceVerifier.verifyAliasSentence sentence
            & Trans.lift . SentenceVerifier.liftSentenceVerifier verifiedModule'
        attrs <- parseAttributes' $ sentenceAliasAttributes verified
        return $ addAlias verified attrs verifiedModule'
      where
        addAlias verified attrs =
            Lens.over
                (field @"indexedModuleAliasSentences")
                (Map.insert (aliasName verified) (attrs, verified))

verifyAliasDependencies
    :: VerifiedModule'
    -> SentenceAlias ParsedPattern
    -> AliasVerifierT Verifier VerifiedModule'
verifyAliasDependencies verifiedModule sentence = do
    deps <- Recursive.fold collectAliasIds aliasPattern
    Monad.foldM verifyAlias verifiedModule deps
  where
    aliasPattern = sentenceAliasRightPattern sentence

collectAliasIds
    :: Monad monad
    => Base ParsedPattern (AliasVerifierT monad (Set Id))
    -> AliasVerifierT monad (Set Id)
collectAliasIds base = do
    _ :< patternF <- sequence base
    let names = Foldable.fold patternF
    AliasContext { aliases } <- Reader.ask
    case patternF of
        ApplicationF application | Map.member name aliases ->
            return $ Set.insert name names
          where
            name =
                symbolOrAliasConstructor
                . applicationSymbolOrAlias
                $ application
        _ -> return names

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

verifyHookedSorts
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyHookedSorts sentences verifiedModule =
    Monad.foldM verifyHookedSort verifiedModule
    $ mapMaybe projectSentenceHookedSort sentences

{- | Find the attributes for the named sort.

It is an error to use this before 'verifySorts'.

 -}
lookupSortAttributesHere
    :: Id
    -> VerifiedModule'
    -> Attribute.Sort
lookupSortAttributesHere name verifiedModule =
    Map.lookup name (indexedModuleSortDescriptions verifiedModule)
    & maybe (error $ noSort name) fst

verifyHookedSort
    :: VerifiedModule'
    -> SentenceSort ParsedPattern
    -> Verifier VerifiedModule'
verifyHookedSort verifiedModule sentence =
    withSentenceHookContext (SentenceHookedSort sentence) $ do
        let SentenceSort { sentenceSortAttributes } = sentence
        VerifierContext { attributesVerification } <- Reader.ask
        hook <-
            verifySortHookAttribute
                attributesVerification
                sentenceSortAttributes
        let SentenceSort { sentenceSortName = name } = sentence
            attrs = lookupSortAttributesHere name verifiedModule
        VerifierContext { builtinVerifiers } <- Reader.ask
        Builtin.sortDeclVerifier
            builtinVerifiers
            hook
            (IndexedModule.eraseAttributes verifiedModule)
            sentence
            attrs
            & either throwError return
        return $ addIndexedModuleHook name hook verifiedModule

verifySymbols
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifySymbols sentences verifiedModule =
    Monad.foldM verifySymbol verifiedModule
    $ mapMaybe project sentences
  where
    project sentence =
        projectSentenceSymbol sentence <|> projectSentenceHookedSymbol sentence

verifySymbol
    :: VerifiedModule'
    -> SentenceSymbol ParsedPattern
    -> Verifier VerifiedModule'
verifySymbol verifiedModule sentence =
    withSentenceSymbolContext sentence $ do
        verified <-
            SentenceVerifier.verifySymbolSentence sentence
            & SentenceVerifier.liftSentenceVerifier verifiedModule
        attrs <- parseAttributes' $ sentenceSymbolAttributes sentence
        return $ addSymbol verified attrs verifiedModule
  where
    addSymbol verified attrs =
        Lens.over
            (field @"indexedModuleSymbolSentences")
            (Map.insert name (attrs, verified))
      where
        Symbol { symbolConstructor = name } = sentenceSymbolSymbol verified

verifyHookedSymbols
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyHookedSymbols sentences verifiedModule =
    Monad.foldM verifyHookedSymbol verifiedModule
    $ mapMaybe projectSentenceHookedSymbol sentences

verifyHookedSymbol
    :: VerifiedModule'
    -> SentenceSymbol ParsedPattern
    -> Verifier VerifiedModule'
verifyHookedSymbol verifiedModule sentence =
    withSentenceHookContext (SentenceHookedSymbol sentence) $ do
        let SentenceSymbol { sentenceSymbolAttributes } = sentence
        VerifierContext { attributesVerification } <- Reader.ask
        hook <-
            verifySymbolHookAttribute
                attributesVerification
                sentenceSymbolAttributes
        VerifierContext { builtinVerifiers } <- Reader.ask
        Builtin.runSymbolVerifier
            (Builtin.symbolVerifier builtinVerifiers hook)
            (findIndexedSort verifiedModule)
            sentence
            & either throwError return
        let Symbol { symbolConstructor = name } = sentenceSymbolSymbol sentence
        return $ addIndexedModuleHook name hook verifiedModule

verifyAxioms
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyAxioms sentences verifiedModule =
    Monad.foldM verifyAxiom verifiedModule
    $ mapMaybe projectSentenceAxiom sentences

verifyAxiom
    :: VerifiedModule'
    -> SentenceAxiom ParsedPattern
    -> Verifier VerifiedModule'
verifyAxiom verifiedModule sentence =
    withSentenceAxiomContext sentence $ do
        verified <-
            SentenceVerifier.verifyAxiomSentence sentence
            & SentenceVerifier.liftSentenceVerifier verifiedModule
        attrs <- parseAttributes' $ sentenceAxiomAttributes sentence
        return $ addAxiom verified attrs verifiedModule
  where
    addAxiom verified attrs =
        Lens.over
            (field @"indexedModuleAxioms")
            ((attrs, verified) :)

verifyClaims
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyClaims sentences verifiedModule =
    Monad.foldM verifyClaim verifiedModule
    $ mapMaybe projectSentenceClaim sentences

verifyClaim
    :: VerifiedModule'
    -> SentenceClaim ParsedPattern
    -> Verifier VerifiedModule'
verifyClaim verifiedModule sentence =
    withSentenceClaimContext sentence $ do
        verified <-
            SentenceVerifier.verifyClaimSentence sentence
            & SentenceVerifier.liftSentenceVerifier verifiedModule
        attrs <- parseAttributes' $ sentenceClaimAttributes sentence
        return $ addClaim verified attrs verifiedModule
  where
    addClaim verified attrs =
        Lens.over
            (field @"indexedModuleClaims")
            ((attrs, verified) :)

verifyNonHooks
    :: [ParsedSentence]
    -> VerifiedModule'
    -> Verifier VerifiedModule'
verifyNonHooks sentences verifiedModule = do
    Foldable.traverse_ verifyNonHook nonHookSentences
    return verifiedModule
  where
    nonHookSentences = mapMaybe project sentences
    project (SentenceHookSentence _) = Nothing
    project sentence = Just sentence

verifyNonHook :: ParsedSentence -> Verifier ()
verifyNonHook sentence =
    withSentenceContext sentence $ do
        VerifierContext { attributesVerification } <- Reader.ask
        verifyNoHookAttribute attributesVerification
            $ sentenceAttributes sentence
