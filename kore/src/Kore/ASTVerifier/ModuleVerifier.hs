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
    , ModuleVerifier
    , runModuleVerifier
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
import           Control.Monad.RWS.Strict
                 ( MonadReader, MonadState, RWST, runRWST )
import qualified Control.Monad.State.Strict as State
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
import qualified Kore.Attribute.Axiom as Attribute
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

type ImplicitModule =
    ImplicitIndexedModule
        Verified.Pattern
        Attribute.Symbol
        Attribute.Axiom

type AttributesVerification' =
    AttributesVerification Attribute.Symbol Attribute.Axiom

data ModuleContext =
    ModuleContext
        { implicitModule         :: !(Maybe ImplicitModule)
        , modules                :: !(Map ModuleName (Module ParsedSentence))
        , importing              :: !(Set ModuleName)
        , attributesVerification :: !AttributesVerification'
        , builtinVerifiers       :: !Builtin.Verifiers
        }
    deriving (GHC.Generic)

type VerifiedModule' = VerifiedModule Attribute.Symbol Attribute.Axiom

data ModuleState =
    ModuleState
        { verifiedModules :: !(Map ModuleName VerifiedModule')
        }
    deriving (GHC.Generic)

newtype ModuleVerifier a =
    ModuleVerifier
        { getModuleVerifier
            ::  RWST ModuleContext () ModuleState
                    (Either (Error VerifyError)) a
        }
    deriving (Functor, Applicative, Monad)

deriving instance MonadReader ModuleContext ModuleVerifier

deriving instance MonadState ModuleState ModuleVerifier

deriving instance MonadError (Error VerifyError) ModuleVerifier

runModuleVerifier
    :: ModuleVerifier a
    -> Maybe ImplicitModule
    -> Map ModuleName (Module ParsedSentence)
    -> AttributesVerification'
    -> Builtin.Verifiers
    -> Either (Error VerifyError) (a, Map ModuleName VerifiedModule')
runModuleVerifier
    moduleVerifier
    implicitModule
    modules
    attributesVerification
    builtinVerifiers
  = do
    (a, moduleState', ()) <-
        runRWST
            (getModuleVerifier moduleVerifier)
            moduleContext
            moduleState
    return (a, verifiedModules moduleState')
  where
    moduleState = ModuleState { verifiedModules = Map.empty }
    moduleContext =
        ModuleContext
            { implicitModule
            , modules
            , importing = Set.empty
            , attributesVerification
            , builtinVerifiers
            }

lookupVerifiedModule :: ModuleName -> ModuleVerifier (Maybe VerifiedModule')
lookupVerifiedModule name = State.gets (Map.lookup name . verifiedModules)

lookupParsedModule :: ModuleName -> ModuleVerifier (Module ParsedSentence)
lookupParsedModule name =
    Reader.asks (Map.lookup name . modules) >>= maybe notFound return
  where
    notFound = koreFail "Module not found."

whileImporting :: ModuleName -> ModuleVerifier a -> ModuleVerifier a
whileImporting name =
    Reader.local $ Lens.over (field @"importing") (Set.insert name)

newIndexedModule :: Module ParsedSentence -> ModuleVerifier VerifiedModule'
newIndexedModule module' = do
    ModuleContext { implicitModule } <- Reader.ask
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

verifyModuleByName :: ModuleName -> ModuleVerifier VerifiedModule'
verifyModuleByName name =
    withContext moduleContext $ do
        checkImportCycle
        lookupVerifiedModule name >>= maybe notYetIndexed alreadyIndexed
  where
    moduleContext = "module '" ++ getModuleNameForError name ++ "'"
    checkImportCycle = do
        isCycle <- Reader.asks (Set.member name . importing)
        koreFailWhen isCycle "Circular module import dependency."
    alreadyIndexed = return
    notYetIndexed = whileImporting name $ do
        module' <- lookupParsedModule name
        let Module { moduleSentences } = module'
            sentences = List.sort moduleSentences
        indexedModule <-
            -- TODO: Refactor this in a type-safe way.
                newIndexedModule module'
            -- TODO: The corresponding functions in
            -- Kore.IndexedModule.IndexedModule can go away.
            >>= verifyImports        sentences
            >>= verifySorts          sentences
            >>= verifySymbols        sentences
            >>= verifyHookedSorts    sentences
            >>= verifyHookedSymbols  sentences
            >>= verifyAliases        sentences
            >>= verifyAxioms         sentences
            >>= verifyClaims         sentences
        _ <- internalIndexedModuleSubsorts indexedModule
        field @"verifiedModules" %= Map.insert name indexedModule
        return indexedModule

verifyImports
    :: [ParsedSentence]
    -> VerifiedModule'
    -> ModuleVerifier VerifiedModule'
verifyImports sentences verifiedModule =
    Monad.foldM verifyImport verifiedModule
    $ mapMaybe projectSentenceImport sentences

verifyImport
    :: VerifiedModule'
    -> SentenceImport ParsedPattern
    -> ModuleVerifier VerifiedModule'
verifyImport verifiedModule sentence =
    withSentenceImportContext sentence $ do
        let SentenceImport { sentenceImportAttributes = attrs0 } = sentence
        attrs1 <- parseAttributes' attrs0
        verified <- verifyModuleByName $ sentenceImportModuleName sentence
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
    -> ModuleVerifier VerifiedModule'
verifySorts sentences verifiedModule =
    Monad.foldM verifySort verifiedModule
    $ mapMaybe project sentences
  where
    project sentence =
        projectSentenceSort sentence <|> projectSentenceHookedSort sentence

verifySort
    :: VerifiedModule'
    -> SentenceSort ParsedPattern
    -> ModuleVerifier VerifiedModule'
verifySort verifiedModule sentence =
    withSentenceSortContext sentence $ do
        verified <-
            liftSentenceVerifier verifiedModule
            $ SentenceVerifier.verifySortSentence sentence
        attrs <- parseAttributes' $ sentenceSortAttributes verified
        return $ addSort verified attrs verifiedModule
  where
    addSort verified attrs =
        Lens.over
            (field @"indexedModuleSortDescriptions")
            (Map.insert name (attrs, verified))
      where
        name = sentenceSortName verified

verifyAliases
    :: [ParsedSentence]
    -> VerifiedModule'
    -> ModuleVerifier VerifiedModule'
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
    -> AliasVerifierT ModuleVerifier (Maybe VerifiedAlias)
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
    -> AliasVerifierT ModuleVerifier VerifiedModule'
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
            Trans.lift . liftSentenceVerifier verifiedModule'
            $ SentenceVerifier.verifyAliasSentence sentence
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
    -> AliasVerifierT ModuleVerifier VerifiedModule'
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
    -> ModuleVerifier VerifiedModule'
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
    -> ModuleVerifier VerifiedModule'
verifyHookedSort verifiedModule sentence =
    withSentenceHookContext (SentenceHookedSort sentence) $ do
        let SentenceSort { sentenceSortAttributes } = sentence
        ModuleContext { attributesVerification } <- Reader.ask
        hook <-
            verifySortHookAttribute
                attributesVerification
                sentenceSortAttributes
        let SentenceSort { sentenceSortName = name } = sentence
            attrs = lookupSortAttributesHere name verifiedModule
        ModuleContext { builtinVerifiers } <- Reader.ask
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
    -> ModuleVerifier VerifiedModule'
verifySymbols sentences verifiedModule =
    Monad.foldM verifySymbol verifiedModule
    $ mapMaybe project sentences
  where
    project sentence =
        projectSentenceSymbol sentence <|> projectSentenceHookedSymbol sentence

verifySymbol
    :: VerifiedModule'
    -> SentenceSymbol ParsedPattern
    -> ModuleVerifier VerifiedModule'
verifySymbol verifiedModule sentence =
    withSentenceSymbolContext sentence $ do
        verified <-
            liftSentenceVerifier verifiedModule
            $ SentenceVerifier.verifySymbolSentence sentence
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
    -> ModuleVerifier VerifiedModule'
verifyHookedSymbols sentences verifiedModule =
    Monad.foldM verifyHookedSymbol verifiedModule
    $ mapMaybe projectSentenceHookedSymbol sentences

verifyHookedSymbol
    :: VerifiedModule'
    -> SentenceSymbol ParsedPattern
    -> ModuleVerifier VerifiedModule'
verifyHookedSymbol verifiedModule sentence =
    withSentenceHookContext (SentenceHookedSymbol sentence) $ do
        let SentenceSymbol { sentenceSymbolAttributes } = sentence
        ModuleContext { attributesVerification } <- Reader.ask
        hook <-
            verifySymbolHookAttribute
                attributesVerification
                sentenceSymbolAttributes
        ModuleContext { builtinVerifiers } <- Reader.ask
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
    -> ModuleVerifier VerifiedModule'
verifyAxioms sentences verifiedModule =
    Monad.foldM verifyAxiom verifiedModule
    $ mapMaybe projectSentenceAxiom sentences

verifyAxiom
    :: VerifiedModule'
    -> SentenceAxiom ParsedPattern
    -> ModuleVerifier VerifiedModule'
verifyAxiom verifiedModule sentence =
    withSentenceAxiomContext sentence $ do
        verified <-
            liftSentenceVerifier verifiedModule
            $ SentenceVerifier.verifyAxiomSentence sentence
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
    -> ModuleVerifier VerifiedModule'
verifyClaims sentences verifiedModule =
    Monad.foldM verifyClaim verifiedModule
    $ mapMaybe projectSentenceClaim sentences

verifyClaim
    :: VerifiedModule'
    -> SentenceClaim ParsedPattern
    -> ModuleVerifier VerifiedModule'
verifyClaim verifiedModule sentence =
    withSentenceClaimContext sentence $ do
        verified <-
            liftSentenceVerifier verifiedModule
            $ SentenceVerifier.verifyClaimSentence sentence
        attrs <- parseAttributes' $ sentenceClaimAttributes sentence
        return $ addClaim verified attrs verifiedModule
  where
    addClaim verified attrs =
        Lens.over
            (field @"indexedModuleClaims")
            ((attrs, verified) :)

liftSentenceVerifier
    :: VerifiedModule'
    -> SentenceVerifier.SentenceVerifier a
    -> ModuleVerifier a
liftSentenceVerifier verifiedModule sentenceVerifier = do
    ModuleContext { attributesVerification, builtinVerifiers } <- Reader.ask
    ModuleVerifier . Trans.lift
        $ SentenceVerifier.runSentenceVerifier
            sentenceVerifier
            verifiedModule
            attributesVerification
            builtinVerifiers
