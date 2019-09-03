{-|
Module      : Kore.ASTVerifier.SentenceVerifier
Description : Tools for verifying the wellformedness of a Kore 'Sentence'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.SentenceVerifier
    ( verifyUniqueNames
    , verifySentences
    , noConstructorWithDomainValuesMessage
    , SentenceVerifier
    , runSentenceVerifier
    , verifySortSentence
    , verifySymbolSentence
    , verifyAliasSentence
    , verifyAxiomSentence
    , verifyClaimSentence
    , verifyHookedSort
    , verifyHookedSymbol
    ) where

import           Control.Monad
                 ( foldM )
import           Control.Monad.Reader
                 ( MonadReader, ReaderT, runReaderT )
import qualified Control.Monad.Reader as Reader
import           Data.Function
import qualified Data.Map as Map
import           Data.Maybe
                 ( isJust )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Error
import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.PatternVerifier as PatternVerifier
import           Kore.ASTVerifier.SortVerifier
import qualified Kore.Attribute.Constructor as Attribute
import qualified Kore.Attribute.Hook as Attribute
import qualified Kore.Attribute.Parser as Attribute.Parser
import qualified Kore.Attribute.Sort as Attribute.Sort
import qualified Kore.Attribute.Sort as Attribute
                 ( Sort )
import qualified Kore.Attribute.Sort.HasDomainValues as Attribute.HasDomainValues
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule as IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Sort
import           Kore.Syntax.Definition
import qualified Kore.Verified as Verified

{-|'verifyUniqueNames' verifies that names defined in a list of sentences are
unique both within the list and outside, using the provided name set.
-}
verifyUniqueNames
    :: [Sentence pat]
    -> Map.Map Text AstLocation
    -- ^ Names that are already defined.
    -> Either (Error VerifyError) (Map.Map Text AstLocation)
    -- ^ On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
verifyUniqueNames sentences existingNames =
    foldM verifyUniqueId existingNames definedNames
  where
    definedNames =
        concatMap definedNamesForSentence sentences

data UnparameterizedId = UnparameterizedId
    { unparameterizedIdName     :: Text
    , unparameterizedIdLocation :: AstLocation
    }
    deriving (Show)

toUnparameterizedId :: Id -> UnparameterizedId
toUnparameterizedId Id {getId = name, idLocation = location} =
    UnparameterizedId
        { unparameterizedIdName = name
        , unparameterizedIdLocation = location
        }

verifyUniqueId
    :: Map.Map Text AstLocation
    -> UnparameterizedId
    -> Either (Error VerifyError) (Map.Map Text AstLocation)
verifyUniqueId existing (UnparameterizedId name location) =
    case Map.lookup name existing of
        Just location' ->
            koreFailWithLocations [location, location']
                ("Duplicated name: '" <> name <> "'.")
        _ -> Right (Map.insert name location existing)

definedNamesForSentence :: Sentence pat -> [UnparameterizedId]
definedNamesForSentence (SentenceAliasSentence sentenceAlias) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForSentence (SentenceSymbolSentence sentenceSymbol) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForSentence (SentenceImportSentence _) = []
definedNamesForSentence (SentenceAxiomSentence _)  = []
definedNamesForSentence (SentenceClaimSentence _)  = []
definedNamesForSentence (SentenceSortSentence sentenceSort) =
    [ toUnparameterizedId (sentenceSortName sentenceSort) ]
definedNamesForSentence (SentenceHookSentence (SentenceHookedSort sentence)) =
    definedNamesForSentence (SentenceSortSentence sentence)
definedNamesForSentence (SentenceHookSentence (SentenceHookedSymbol sentence)) =
    definedNamesForSentence (SentenceSymbolSentence sentence)

data SentenceContext =
    forall axiomAttrs.
    SentenceContext
        { indexedModule :: !(VerifiedModule Attribute.Symbol axiomAttrs)
            -- TODO: Make indexedModule a "state" field.
        , attributesVerification
            :: !(AttributesVerification Attribute.Symbol axiomAttrs)
        -- ^ The indexed Kore module containing all definitions in scope.
        , builtinVerifiers :: !Builtin.Verifiers
        }

newtype SentenceVerifier a =
    SentenceVerifier
        { getSentenceVerifier
            :: ReaderT SentenceContext (Either (Error VerifyError)) a
        }
    deriving (Applicative, Functor, Monad)

deriving instance MonadReader SentenceContext SentenceVerifier

deriving instance e ~ VerifyError => MonadError (Error e) SentenceVerifier

{- | Look up a sort declaration.
 -}
findSort :: Id -> SentenceVerifier (SentenceSort Verified.Pattern)
findSort identifier = do
    SentenceContext { indexedModule } <- Reader.ask
    findIndexedSort indexedModule identifier

{- | Look up a sort declaration outside 'SentenceVerifier'.

@askFindSort@ captures the current context so that the function it returns can
be used in another context.

 -}
askFindSort
    :: MonadError (Error e) error
    => SentenceVerifier (Id -> error (SentenceSort Verified.Pattern))
askFindSort = do
    SentenceContext { indexedModule } <- Reader.ask
    return (findIndexedSort indexedModule)

{- | Construct a 'PatternVerifier.Context' in the current 'SentenceContext'.
 -}
askPatternContext
    :: Set SortVariable  -- ^ Declared sort variables
    -> SentenceVerifier PatternVerifier.Context
askPatternContext variables = do
    SentenceContext { indexedModule, builtinVerifiers } <- Reader.ask
    return PatternVerifier.Context
        { builtinDomainValueVerifiers =
            Builtin.domainValueVerifiers builtinVerifiers
        , indexedModule =
            indexedModule
            -- & IndexedModule.erasePatterns
            & IndexedModule.eraseAxiomAttributes
        , declaredSortVariables = variables
        , declaredVariables = emptyDeclaredVariables
        }

runSentenceVerifier
    :: SentenceVerifier a
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> AttributesVerification Attribute.Symbol axiomAttrs
    -> Builtin.Verifiers
    -> Either (Error VerifyError) a
runSentenceVerifier
    sentenceVerifier
    indexedModule
    attributesVerification
    builtinVerifiers
  =
    runReaderT (getSentenceVerifier sentenceVerifier) sentenceContext
  where
    sentenceContext =
        SentenceContext
            { indexedModule
            , attributesVerification
            , builtinVerifiers
            }

{-|'verifySentences' verifies the welformedness of a list of Kore 'Sentence's.
-}
verifySentences
    :: VerifiedModule Attribute.Symbol axiomAtts
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> AttributesVerification Attribute.Symbol axiomAtts
    -> Builtin.Verifiers
    -> [ParsedSentence]
    -> Either (Error VerifyError) [Verified.Sentence]
verifySentences
    indexedModule
    attributesVerification
    builtinVerifiers
    sentences
  =
    runSentenceVerifier
        (traverse verifySentence sentences)
        indexedModule
        attributesVerification
        builtinVerifiers

verifySentence :: ParsedSentence -> SentenceVerifier Verified.Sentence
verifySentence sentence =
    withSentenceContext sentence verifySentenceWorker
  where
    verifySentenceWorker :: SentenceVerifier Verified.Sentence
    verifySentenceWorker = do
        verified <-
            case sentence of
                SentenceSymbolSentence symbolSentence ->
                    SentenceSymbolSentence
                        <$> verifySymbolSentence symbolSentence
                SentenceAliasSentence aliasSentence ->
                    SentenceAliasSentence
                        <$> verifyAliasSentence aliasSentence
                SentenceAxiomSentence axiomSentence ->
                    SentenceAxiomSentence
                        <$> verifyAxiomSentence axiomSentence
                SentenceClaimSentence claimSentence ->
                    SentenceClaimSentence
                        <$> verifyClaimSentence claimSentence
                SentenceImportSentence importSentence ->
                    -- Since we have an IndexedModule, we assume that imports
                    -- were already resolved, so there is nothing left to verify
                    -- here.
                    SentenceImportSentence
                        <$> traverse verifyNoPatterns importSentence
                SentenceSortSentence sortSentence ->
                    SentenceSortSentence
                        <$> verifySortSentence sortSentence
                SentenceHookSentence hookSentence ->
                    SentenceHookSentence
                        <$> verifyHookSentence hookSentence
        verifySentenceAttributes sentence
        return verified

verifySentenceAttributes
    :: ParsedSentence
    -> SentenceVerifier VerifySuccess
verifySentenceAttributes sentence =
    do
        SentenceContext { attributesVerification } <- Reader.ask
        let attributes = sentenceAttributes sentence
        verifyAttributes attributes attributesVerification
        case sentence of
            SentenceHookSentence _ -> return ()
            _ -> verifyNoHookAttribute attributesVerification attributes
        verifySuccess

verifyHookSentence
    :: ParsedSentenceHook -> SentenceVerifier Verified.SentenceHook
verifyHookSentence (SentenceHookedSort s) =
    SentenceHookedSort <$> verifyHookedSort s
verifyHookSentence (SentenceHookedSymbol s) =
    SentenceHookedSymbol <$> verifyHookedSymbol s

verifyHookedSort :: ParsedSentenceSort -> SentenceVerifier Verified.SentenceSort
verifyHookedSort sentence@SentenceSort { sentenceSortAttributes } = do
    verified <- verifySortSentence sentence
    SentenceContext { attributesVerification, builtinVerifiers } <- Reader.ask
    hook <-
        verifySortHookAttribute
            attributesVerification
            sentenceSortAttributes
    attrs <-
        Attribute.Parser.liftParser
        $ Attribute.Parser.parseAttributes sentenceSortAttributes
    SentenceContext { indexedModule } <- Reader.ask
    Builtin.sortDeclVerifier
        builtinVerifiers
        hook
        (IndexedModule.eraseAttributes indexedModule)
        sentence
        attrs
        & either throwError return
    return verified

verifyHookedSymbol
    :: ParsedSentenceSymbol -> SentenceVerifier Verified.SentenceSymbol
verifyHookedSymbol sentence@SentenceSymbol { sentenceSymbolAttributes } = do
    verified <- verifySymbolSentence sentence
    SentenceContext { attributesVerification, builtinVerifiers } <- Reader.ask
    hook <-
        verifySymbolHookAttribute
            attributesVerification
            sentenceSymbolAttributes
    findSort' <- askFindSort
    Builtin.runSymbolVerifier
        (Builtin.symbolVerifier builtinVerifiers hook)
        findSort'
        sentence
        & either throwError return
    return verified

verifySymbolSentence
    :: ParsedSentenceSymbol
    -> SentenceVerifier Verified.SentenceSymbol
verifySymbolSentence sentence =
    do
        variables <- buildDeclaredSortVariables sortParams
        mapM_
            (verifySort findSort variables)
            (sentenceSymbolSorts sentence)
        verifyConstructorNotInHookedOrDvSort
        verifySort
            findSort
            variables
            (sentenceSymbolResultSort sentence)
        traverse verifyNoPatterns sentence
  where
    sortParams = (symbolParams . sentenceSymbolSymbol) sentence

    verifyConstructorNotInHookedOrDvSort :: SentenceVerifier ()
    verifyConstructorNotInHookedOrDvSort = do
        SentenceContext { indexedModule } <- Reader.ask
        let
            symbol = symbolConstructor $ sentenceSymbolSymbol sentence
            attributes = sentenceSymbolAttributes sentence
            resultSort = sentenceSymbolResultSort sentence
            resultSortId = getSortId resultSort

            -- TODO(vladimir.ciobanu): Lookup this attribute in the symbol
            -- attribute record when it becomes available.
            isCtor =
                Attribute.constructorAttribute  `elem` getAttributes attributes
            sortData = do
                (sortDescription, _) <-
                    Map.lookup resultSortId
                        $ indexedModuleSortDescriptions indexedModule
                return
                    (maybeHook sortDescription, hasDomainValues sortDescription)
        case sortData of
            Nothing -> return ()
            Just (resultSortHook, resultHasDomainValues) -> do
                koreFailWhen
                    (isCtor && isJust resultSortHook)
                    ( "Cannot define constructor '"
                    ++ getIdForError symbol
                    ++ "' for hooked sort '"
                    ++ getIdForError resultSortId
                    ++ "'."
                    )
                koreFailWhen
                    (isCtor && resultHasDomainValues)
                    (noConstructorWithDomainValuesMessage symbol resultSort)

maybeHook :: Attribute.Sort -> Maybe Text
maybeHook = Attribute.getHook . Attribute.Sort.hook

hasDomainValues :: Attribute.Sort -> Bool
hasDomainValues =
    Attribute.HasDomainValues.getHasDomainValues
    . Attribute.Sort.hasDomainValues

verifyAliasSentence
    :: ParsedSentenceAlias
    -> SentenceVerifier Verified.SentenceAlias
verifyAliasSentence sentence = do
    variables <- buildDeclaredSortVariables sortParams
    mapM_ (verifySort findSort variables) sentenceAliasSorts
    verifySort findSort variables sentenceAliasResultSort
    context <- askPatternContext variables
    either throwError return . runPatternVerifier context $ do
        (declaredVariables, verifiedLeftPattern) <-
            verifyAliasLeftPattern alias sentenceAliasSorts leftPattern
        verifiedRightPattern <-
            withDeclaredVariables declaredVariables
            $ verifyPattern (Just expectedSort) rightPattern
        return sentence
            { sentenceAliasLeftPattern = verifiedLeftPattern
            , sentenceAliasRightPattern = verifiedRightPattern
            }
  where
    SentenceAlias { sentenceAliasAlias = alias } = sentence
    SentenceAlias { sentenceAliasLeftPattern = leftPattern } = sentence
    SentenceAlias { sentenceAliasRightPattern = rightPattern } = sentence
    SentenceAlias { sentenceAliasSorts } = sentence
    SentenceAlias { sentenceAliasResultSort } = sentence
    sortParams   = (aliasParams . sentenceAliasAlias) sentence
    expectedSort = sentenceAliasResultSort

verifyAxiomSentence
    :: ParsedSentenceAxiom
    -> SentenceVerifier Verified.SentenceAxiom
verifyAxiomSentence axiom = do
    variables <- buildDeclaredSortVariables $ sentenceAxiomParameters axiom
    context <- askPatternContext variables
    verifiedAxiomPattern <-
        either throwError return
        . runPatternVerifier context
        $ verifyStandalonePattern Nothing sentenceAxiomPattern
    return axiom { sentenceAxiomPattern = verifiedAxiomPattern }
  where
    SentenceAxiom { sentenceAxiomPattern } = axiom

verifyClaimSentence
    :: SentenceClaim ParsedPattern
    -> SentenceVerifier Verified.SentenceClaim
verifyClaimSentence claimSentence =
    SentenceClaim <$> verifyAxiomSentence (getSentenceClaim claimSentence)

verifySortSentence
    :: ParsedSentenceSort
    -> SentenceVerifier Verified.SentenceSort
verifySortSentence sentenceSort = do
    _ <- buildDeclaredSortVariables (sentenceSortParameters sentenceSort)
    traverse verifyNoPatterns sentenceSort

buildDeclaredSortVariables
    :: MonadError (Error e) error
    => [SortVariable]
    -> error (Set.Set SortVariable)
buildDeclaredSortVariables [] = return Set.empty
buildDeclaredSortVariables (unifiedVariable : list) = do
    variables <- buildDeclaredSortVariables list
    koreFailWithLocationsWhen
        (unifiedVariable `Set.member` variables)
        [unifiedVariable]
        (  "Duplicated sort variable: '"
        <> extractVariableName unifiedVariable
        <> "'.")
    return (Set.insert unifiedVariable variables)
  where
    extractVariableName variable = getId (getSortVariable variable)
