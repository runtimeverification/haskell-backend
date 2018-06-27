{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs                 #-}
{-|
Module      : Data.Kore.ASTVerifier.SentenceVerifier
Description : Tools for verifying the wellformedness of a Kore 'Sentence'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.SentenceVerifier ( verifyUniqueNames
                                              , verifySentences
                                              ) where

import           Control.Monad                            (foldM)
import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.Error
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.ASTHelpers
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.Resolvers

import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set

{-|'verifyUniqueNames' verifies that names defined in a list of sentences are
unique both within the list and outside, using the provided name set.
-}
verifyUniqueNames
    :: [KoreSentence]
    -> Map.Map String AstLocation
    -- ^ Names that are already defined.
    -> Either (Error VerifyError) (Map.Map String AstLocation)
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
        { unparameterizedIdName = name
        , unparameterizedIdLocation = location
        }

verifyUniqueId
    :: Map.Map String AstLocation
    -> UnparameterizedId
    -> Either (Error VerifyError) (Map.Map String AstLocation)
verifyUniqueId existing (UnparameterizedId name location) =
    case Map.lookup name existing of
        Just location' ->
            koreFailWithLocations [location, location']
                ("Duplicated name: '" ++ name ++ "'.")
        _ -> Right (Map.insert name location existing)

definedNamesForSentence :: KoreSentence -> [UnparameterizedId]
definedNamesForSentence =
    applyUnifiedSentence
        definedNamesForMetaSentence
        definedNamesForObjectSentence

definedNamesForMetaSentence
    :: Sentence Meta sortParam pat variable -> [UnparameterizedId]
definedNamesForMetaSentence (SentenceAliasSentence sentenceAlias) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForMetaSentence (SentenceSymbolSentence sentenceSymbol) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForMetaSentence (SentenceImportSentence _) = []
definedNamesForMetaSentence (SentenceAxiomSentence _)  = []

definedNamesForObjectSentence
    :: Sentence Object sortParam pat variable -> [UnparameterizedId]
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
    :: KoreIndexedModule
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> AttributesVerification
    -> [KoreSentence]
    -> Either (Error VerifyError) VerifySuccess
verifySentences
    indexedModule attributesVerification sentences
  = do
    mapM_ (verifySentence indexedModule attributesVerification) sentences
    verifySuccess

verifySentence
    :: KoreIndexedModule
    -> AttributesVerification
    -> KoreSentence
    -> Either (Error VerifyError) VerifySuccess
verifySentence indexedModule attributesVerification =
    applyUnifiedSentence
        (verifyMetaSentence indexedModule attributesVerification)
        (verifyObjectSentence indexedModule attributesVerification)

verifyMetaSentence
    :: KoreIndexedModule
    -> AttributesVerification
    -> Sentence Meta UnifiedSortVariable UnifiedPattern Variable
    -> Either (Error VerifyError) VerifySuccess
verifyMetaSentence
    indexedModule
    attributesVerification
    (SentenceAliasSentence aliasSentence)
  =
    verifyAliasSentence
        (resolveSort indexedModule)
        indexedModule
        attributesVerification
        aliasSentence
verifyMetaSentence
    indexedModule
    attributesVerification
    (SentenceSymbolSentence symbolSentence)
  =
    verifySymbolSentence
        (resolveSort indexedModule)
        indexedModule
        attributesVerification
        symbolSentence
verifyMetaSentence
    indexedModule
    attributesVerification
    (SentenceAxiomSentence axiomSentence)
  =
    verifyAxiomSentence axiomSentence indexedModule attributesVerification
verifyMetaSentence _ _ (SentenceImportSentence _) =
    -- Since we have an IndexedModule, we assume that imports were already
    -- resolved, so there is nothing left to verify here.
    verifySuccess

verifyObjectSentence
    :: KoreIndexedModule
    -> AttributesVerification
    -> Sentence Object UnifiedSortVariable UnifiedPattern Variable
    -> Either (Error VerifyError) VerifySuccess
verifyObjectSentence
    indexedModule
    attributesVerification
    (SentenceAliasSentence aliasSentence)
  =
    verifyAliasSentence
        (resolveSort indexedModule)
        indexedModule
        attributesVerification
        aliasSentence
verifyObjectSentence
    indexedModule
    attributesVerification
    (SentenceSymbolSentence symbolSentence)
  =
    verifySymbolSentence
        (resolveSort indexedModule)
        indexedModule
        attributesVerification
        symbolSentence
verifyObjectSentence
    _
    attributesVerification
    (SentenceSortSentence sortSentence)
  =
    verifySortSentence sortSentence attributesVerification
verifyObjectSentence
    _
    attributesVerification
    (SentenceHookSentence (SentenceHookedSort sortSentence))
  =
    verifySortSentence sortSentence attributesVerification
verifyObjectSentence
    indexedModule
    attributesVerification
    (SentenceHookSentence (SentenceHookedSymbol symbolSentence))
  =
    verifySymbolSentence
        (resolveSort indexedModule)
        indexedModule
        attributesVerification
        symbolSentence

verifySymbolSentence
    :: (MetaOrObject level)
    => (Id level -> Either (Error VerifyError) (SortDescription level))
    -> KoreIndexedModule
    -> AttributesVerification
    -> KoreSentenceSymbol level
    -> Either (Error VerifyError) VerifySuccess
verifySymbolSentence
    findSortDeclaration _ attributesVerification sentence
  =
    withLocationAndContext
        ((symbolConstructor . sentenceSymbolSymbol) sentence)
        (  "symbol"
        ++ " '"
        ++ getId ((symbolConstructor . sentenceSymbolSymbol) sentence)
        ++ "' declaration"
        )
        (do
            variables <- buildDeclaredSortVariables sortParams
            mapM_
                (verifySort findSortDeclaration variables)
                (sentenceSymbolSorts sentence)
            verifySort
                findSortDeclaration
                variables
                (sentenceSymbolResultSort sentence)
            verifyAttributes
                (sentenceSymbolAttributes sentence)
                attributesVerification
        )
  where
    sortParams = (symbolParams . sentenceSymbolSymbol) sentence

verifyAliasSentence
    :: (MetaOrObject level)
    => (Id level -> Either (Error VerifyError) (SortDescription level))
    -> KoreIndexedModule
    -> AttributesVerification
    -> KoreSentenceAlias level
    -> Either (Error VerifyError) VerifySuccess
verifyAliasSentence
    findSortDeclaration indexedModule attributesVerification sentence
  =
    withLocationAndContext
        (aliasConstructor $ sentenceAliasAlias sentence)
        (  "alias"
        ++ " '"
        ++ getId (aliasConstructor $ sentenceAliasAlias sentence)
        ++ "' declaration"
        )
        (do
            variables <- buildDeclaredSortVariables sortParams
            mapM_
                (verifySort findSortDeclaration variables)
                (sentenceAliasSorts sentence)
            verifySort
                findSortDeclaration
                variables
                (sentenceAliasResultSort sentence)
            if leftPatternSort == rightPatternSort 
                then
                    verifySuccess
                else 
                    koreFail "Left and Right sorts do not match"
            verifyAliasLeftPattern
                (asKorePattern $ sentenceAliasLeftPattern sentence)
                (Just $ (asUnified leftPatternSort))
                indexedModule
                variables
            verifyPattern
                (asKorePattern $ sentenceAliasRightPattern sentence)
                (Just $ (asUnified rightPatternSort))
                indexedModule
                variables
            verifyAttributes
                (sentenceAliasAttributes sentence)
                attributesVerification
        )
  where
    sortParams       = (aliasParams . sentenceAliasAlias) sentence
    leftPatternSort  = patternSort leftPattern
    rightPatternSort = patternSort rightPattern
    headSort         = applicationSortsResult . getHeadApplicationSorts indexedModule
    patternSort      = getPatternResultSort headSort 
    leftPattern      = sentenceAliasLeftPattern sentence
    rightPattern     = sentenceAliasRightPattern sentence

verifyAxiomSentence
    :: KoreSentenceAxiom
    -> KoreIndexedModule
    -> AttributesVerification
    -> Either (Error VerifyError) VerifySuccess
verifyAxiomSentence axiom indexedModule attributesVerification =
    withContext
        "axiom declaration"
        (do
            variables <-
                buildDeclaredUnifiedSortVariables
                    (sentenceAxiomParameters axiom)
            verifyPattern
                (sentenceAxiomPattern axiom)
                Nothing
                indexedModule
                variables
            verifyAttributes
                (sentenceAxiomAttributes axiom)
                attributesVerification
        )

verifySortSentence
    :: KoreSentenceSort
    -> AttributesVerification
    -> Either (Error VerifyError) VerifySuccess
verifySortSentence sentenceSort attributesVerification =
    withLocationAndContext
        (sentenceSortName sentenceSort)
        ("sort '" ++ getId (sentenceSortName sentenceSort) ++ "' declaration")
        (do
            _ <-
                buildDeclaredSortVariables (sentenceSortParameters sentenceSort)
            verifyAttributes
                (sentenceSortAttributes sentenceSort)
                attributesVerification
        )

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
        getId (getSortVariable variable)
    extractVariableName (UnifiedMeta variable) =
        getId (getSortVariable variable)
