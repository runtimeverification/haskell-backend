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
    ) where

import           Control.Monad
                 ( foldM )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Error
import           Kore.AST.Kore
import           Kore.AST.MLPatterns
import           Kore.AST.Sentence
import           Kore.ASTVerifier.AttributesVerifier
import           Kore.ASTVerifier.Error
import           Kore.ASTVerifier.PatternVerifier as PatternVerifier
import           Kore.ASTVerifier.SortVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers

{-|'verifyUniqueNames' verifies that names defined in a list of sentences are
unique both within the list and outside, using the provided name set.
-}
verifyUniqueNames
    :: [KoreSentence]
    -> Map.Map Text AstLocation
    -- ^ Names that are already defined.
    -> Either (Error VerifyError) (Map.Map Text AstLocation)
    -- ^ On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
verifyUniqueNames sentences existingNames =
    foldM verifyUniqueId existingNames
        (concatMap definedNamesForSentence sentences)

data UnparameterizedId = UnparameterizedId
    { unparameterizedIdName     :: String
    , unparameterizedIdLocation :: AstLocation
    }
toUnparameterizedId :: Id level -> UnparameterizedId
toUnparameterizedId Id {getId = name, idLocation = location} =
    UnparameterizedId
        { unparameterizedIdName = Text.unpack name
        , unparameterizedIdLocation = location
        }

verifyUniqueId
    :: Map.Map Text AstLocation
    -> UnparameterizedId
    -> Either (Error VerifyError) (Map.Map Text AstLocation)
verifyUniqueId existing (UnparameterizedId name location) =
    case Map.lookup name' existing of
        Just location' ->
            koreFailWithLocations [location, location']
                ("Duplicated name: '" ++ name ++ "'.")
        _ -> Right (Map.insert name' location existing)
  where
    name' = Text.pack name

definedNamesForSentence :: KoreSentence -> [UnparameterizedId]
definedNamesForSentence =
    applyUnifiedSentence
        definedNamesForMetaSentence
        definedNamesForObjectSentence

definedNamesForMetaSentence
    :: Sentence Meta sortParam pat dom var -> [UnparameterizedId]
definedNamesForMetaSentence (SentenceAliasSentence sentenceAlias) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForMetaSentence (SentenceSymbolSentence sentenceSymbol) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForMetaSentence (SentenceImportSentence _) = []
definedNamesForMetaSentence (SentenceAxiomSentence _)  = []
definedNamesForMetaSentence (SentenceClaimSentence _)  = []
definedNamesForMetaSentence (SentenceSortSentence sentenceSort) =
    [ toUnparameterizedId (sentenceSortName sentenceSort) ]

definedNamesForObjectSentence
    :: Sentence Object sortParam pat dom var -> [UnparameterizedId]
definedNamesForObjectSentence (SentenceAliasSentence sentenceAlias) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForObjectSentence (SentenceSymbolSentence sentenceSymbol) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForObjectSentence (SentenceSortSentence sentenceSort) =
    [ sentenceName
    , UnparameterizedId
        { unparameterizedIdName =
            metaNameForObjectSort (unparameterizedIdName sentenceName)
        , unparameterizedIdLocation =
            AstLocationLifted (unparameterizedIdLocation sentenceName)
        }
    ]
  where sentenceName = toUnparameterizedId (sentenceSortName sentenceSort)
definedNamesForObjectSentence
    (SentenceHookSentence (SentenceHookedSort sentence))
  = definedNamesForObjectSentence (SentenceSortSentence sentence)
definedNamesForObjectSentence
    (SentenceHookSentence (SentenceHookedSymbol sentence))
  = definedNamesForObjectSentence (SentenceSymbolSentence sentence)

{-|'verifySentences' verifies the welformedness of a list of Kore 'Sentence's.
-}
verifySentences
    :: KoreIndexedModule atts
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> AttributesVerification atts
    -> Builtin.Verifiers
    -> [KoreSentence]
    -> Either (Error VerifyError) VerifySuccess
verifySentences
    indexedModule attributesVerification builtinVerifiers sentences
  = do
    mapM_
        (verifySentence
            builtinVerifiers
            indexedModule
            attributesVerification
        )
        sentences
    verifySuccess

verifySentence
    :: Builtin.Verifiers
    -> KoreIndexedModule atts
    -> AttributesVerification atts
    -> KoreSentence
    -> Either (Error VerifyError) VerifySuccess
verifySentence builtinVerifiers indexedModule attributesVerification =
    applyUnifiedSentence
        (verifyMetaSentence builtinVerifiers indexedModule attributesVerification)
        (verifyObjectSentence
            builtinVerifiers
            indexedModule
            attributesVerification
        )

verifyMetaSentence
    :: Builtin.Verifiers
    -> KoreIndexedModule atts
    -> AttributesVerification atts
    -> Sentence Meta UnifiedSortVariable KorePattern Domain.Builtin Variable
    -> Either (Error VerifyError) VerifySuccess
verifyMetaSentence
    builtinVerifiers
    indexedModule
    attributesVerification
    sentence
  =
    withSentenceContext sentence verifyMetaSentence0
  where
    verifyMetaSentence0 = do
        case sentence of
            SentenceSymbolSentence symbolSentence ->
                verifySymbolSentence
                    indexedModule
                    symbolSentence
            SentenceAliasSentence aliasSentence ->
                verifyAliasSentence
                    builtinVerifiers
                    indexedModule
                    aliasSentence
            SentenceAxiomSentence axiomSentence ->
                verifyAxiomSentence
                    axiomSentence
                    builtinVerifiers
                    indexedModule
            SentenceClaimSentence claimSentence ->
                verifyAxiomSentence
                    claimSentence
                    builtinVerifiers
                    indexedModule
            SentenceSortSentence sortSentence -> do
                koreFailWhen
                    (sortParams /= [])
                    ("Malformed meta sort '" ++ getIdForError sortId
                        ++ "' with non-empty Parameter sorts.")
                verifySuccess
              where
                sortId     = sentenceSortName sortSentence
                sortParams = sentenceSortParameters sortSentence
            SentenceImportSentence _ ->
                -- Since we have an IndexedModule, we assume that imports were
                -- already resolved, so there is nothing left to verify here.
                verifySuccess
        verifySentenceAttributes
            attributesVerification
            sentence

verifyObjectSentence
    :: Builtin.Verifiers
    -> KoreIndexedModule atts
    -> AttributesVerification atts
    -> Sentence Object UnifiedSortVariable KorePattern Domain.Builtin Variable
    -> Either (Error VerifyError) VerifySuccess
verifyObjectSentence
    builtinVerifiers
    indexedModule
    attributesVerification
    sentence
  =
    withSentenceContext sentence verifyObjectSentence1
  where
    verifyObjectSentence1 = do
        case sentence of
            SentenceAliasSentence aliasSentence ->
                verifyAliasSentence
                    builtinVerifiers
                    indexedModule
                    aliasSentence
            SentenceSymbolSentence symbolSentence ->
                verifySymbolSentence
                    indexedModule
                    symbolSentence
            SentenceSortSentence sortSentence ->
                verifySortSentence sortSentence
            SentenceHookSentence hookSentence ->
                verifyHookSentence
                    builtinVerifiers
                    indexedModule
                    attributesVerification
                    hookSentence
        verifySentenceAttributes
            attributesVerification
            sentence

verifySentenceAttributes
    :: AttributesVerification atts
    -> Sentence level UnifiedSortVariable KorePattern Domain.Builtin Variable
    -> Either (Error VerifyError) VerifySuccess
verifySentenceAttributes attributesVerification sentence =
    do
        let attributes = sentenceAttributes sentence
        verifyAttributes attributes attributesVerification
        case sentence of
            SentenceHookSentence _ -> return ()
            _ -> verifyNoHookAttribute attributesVerification attributes
        verifySuccess

verifyHookSentence
    :: Builtin.Verifiers
    -> KoreIndexedModule atts
    -> AttributesVerification atts
    -> SentenceHook Object KorePattern Domain.Builtin Variable
    -> Either (Error VerifyError) VerifySuccess
verifyHookSentence
    builtinVerifiers
    indexedModule
    attributesVerification
  =
    \case
        SentenceHookedSort s -> verifyHookedSort s
        SentenceHookedSymbol s -> verifyHookedSymbol s
  where
    verifyHookedSort
        sentence@SentenceSort { sentenceSortAttributes }
      = do
        verifySortSentence sentence
        hook <-
            verifySortHookAttribute
                indexedModule
                attributesVerification
                sentenceSortAttributes
        Builtin.sortDeclVerifier builtinVerifiers hook sentence
        return (VerifySuccess ())

    verifyHookedSymbol
        sentence@SentenceSymbol
            { sentenceSymbolAttributes
            -- , sentenceSymbolSorts
            -- , sentenceSymbolResultSort
            }
      = do
        verifySymbolSentence indexedModule sentence
        hook <-
            verifySymbolHookAttribute
                attributesVerification
                sentenceSymbolAttributes
        Builtin.symbolVerifier builtinVerifiers hook findSort sentence
        return (VerifySuccess ())

    findSort = findIndexedSort indexedModule

verifySymbolSentence
    :: (MetaOrObject level)
    => KoreIndexedModule atts
    -> KoreSentenceSymbol level
    -> Either (Error VerifyError) VerifySuccess
verifySymbolSentence
    indexedModule sentence
  =
    do
        variables <- buildDeclaredSortVariables sortParams
        mapM_
            (verifySort findSort variables)
            (sentenceSymbolSorts sentence)
        verifySort
            findSort
            variables
            (sentenceSymbolResultSort sentence)
  where
    findSort = findIndexedSort indexedModule
    sortParams = (symbolParams . sentenceSymbolSymbol) sentence

verifyAliasSentence
    :: (MetaOrObject level)
    => Builtin.Verifiers
    -> KoreIndexedModule atts
    -> KoreSentenceAlias level
    -> Either (Error VerifyError) VerifySuccess
verifyAliasSentence
    builtinVerifiers indexedModule sentence
  =
    do
        variables <- buildDeclaredSortVariables sortParams
        mapM_
            (verifySort findSort variables)
            (sentenceAliasSorts sentence)
        verifySort
            findSort
            variables
            (sentenceAliasResultSort sentence)
        if leftPatternSort == rightPatternSort
            then
                verifySuccess
            else
                koreFail "Left and Right sorts do not match"
        let context =
                PatternVerifier.Context
                    { builtinPatternVerifier =
                        Builtin.patternVerifier builtinVerifiers
                    , indexedModule = Attribute.Null <$ indexedModule
                    , declaredSortVariables = variables
                    , declaredVariables = emptyDeclaredVariables
                    }
        runPatternVerifier context $ do
            verifyAliasLeftPattern
                (Just $ asUnified leftPatternSort)
                (asCommonKorePattern $ sentenceAliasLeftPattern sentence)
            verifyPattern
                (Just $ asUnified rightPatternSort)
                (asCommonKorePattern $ sentenceAliasRightPattern sentence)
  where
    findSort         = findIndexedSort indexedModule
    sortParams       = (aliasParams . sentenceAliasAlias) sentence
    leftPatternSort  = patternSort leftPattern
    rightPatternSort = patternSort rightPattern
    applicationSorts = getHeadApplicationSorts indexedModule
    patternSort      = getPatternResultSort applicationSorts
    leftPattern      = sentenceAliasLeftPattern sentence
    rightPattern     = sentenceAliasRightPattern sentence

verifyAxiomSentence
    :: KoreSentenceAxiom
    -> Builtin.Verifiers
    -> KoreIndexedModule atts
    -> Either (Error VerifyError) VerifySuccess
verifyAxiomSentence axiom builtinVerifiers indexedModule =
    do
        variables <-
            buildDeclaredUnifiedSortVariables
                (sentenceAxiomParameters axiom)
        let context =
                PatternVerifier.Context
                    { builtinPatternVerifier =
                        Builtin.patternVerifier builtinVerifiers
                    , indexedModule = Attribute.Null <$ indexedModule
                    , declaredSortVariables = variables
                    , declaredVariables = emptyDeclaredVariables
                    }
        runPatternVerifier context $ do
            verifyPattern Nothing (sentenceAxiomPattern axiom)

verifySortSentence
    :: KoreSentenceSort Object
    -> Either (Error VerifyError) VerifySuccess
verifySortSentence sentenceSort = do
    _ <- buildDeclaredSortVariables (sentenceSortParameters sentenceSort)
    verifySuccess

buildDeclaredSortVariables
    :: MetaOrObject level
    => [SortVariable level]
    -> Either (Error VerifyError) (Set.Set UnifiedSortVariable)
buildDeclaredSortVariables variables =
    buildDeclaredUnifiedSortVariables
        (map asUnified variables)

buildDeclaredUnifiedSortVariables
    :: [UnifiedSortVariable]
    -> Either (Error VerifyError) (Set.Set UnifiedSortVariable)
buildDeclaredUnifiedSortVariables [] = Right Set.empty
buildDeclaredUnifiedSortVariables (unifiedVariable : list) = do
    variables <- buildDeclaredUnifiedSortVariables list
    koreFailWithLocationsWhen
        (unifiedVariable `Set.member` variables)
        [unifiedVariable]
        (  "Duplicated sort variable: '"
        ++ extractVariableName unifiedVariable
        ++ "'.")
    return (Set.insert unifiedVariable variables)
  where
    extractVariableName (UnifiedObject variable) =
        getIdForError (getSortVariable variable)
    extractVariableName (UnifiedMeta variable) =
        getIdForError (getSortVariable variable)
