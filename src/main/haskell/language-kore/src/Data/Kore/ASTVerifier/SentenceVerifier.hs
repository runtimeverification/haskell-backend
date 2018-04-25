{-# LANGUAGE GADTs #-}
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
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.ASTVerifier.Resolvers
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Set                                 as Set

{-|'verifyUniqueNames' verifies that names defined in a list of sentences are
unique both within the list and outside, using the provided name set.
-}
verifyUniqueNames
    :: [KoreSentence]
    -> Set.Set String
    -- ^ Names that are already defined.
    -> Either (Error VerifyError) (Set.Set String)
    -- ^ On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
verifyUniqueNames sentences existingNames =
    foldM verifyUniqueName existingNames
        (concatMap definedNamesForSentence sentences)

verifyUniqueName
    :: Set.Set String
    -> String
    -> Either (Error VerifyError) (Set.Set String)
verifyUniqueName set name =
    if name `Set.member` set
        then koreFail ("Duplicated name: '" ++ name ++ "'.")
        else Right (Set.insert name set)

definedNamesForSentence :: KoreSentence -> [String]
definedNamesForSentence (MetaSentence (SentenceAliasSentence sentenceAlias)) =
    [ getId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForSentence (ObjectSentence (SentenceAliasSentence sentenceAlias)) =
    [ getId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForSentence (MetaSentence (SentenceSymbolSentence sentenceSymbol)) =
    [ getId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForSentence (ObjectSentence (SentenceSymbolSentence sentenceSymbol)) =
    [ getId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForSentence (ObjectSentence (SentenceSortSentence sentenceSort)) =
    [sentenceName, metaNameForObjectSort sentenceName]
  where sentenceName = getId (sentenceSortName sentenceSort)
definedNamesForSentence (MetaSentence (SentenceImportSentence _)) = []
definedNamesForSentence (MetaSentence (SentenceAxiomSentence _)) = []

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
verifySentence
    indexedModule
    attributesVerification
    (MetaSentence (SentenceAliasSentence aliasSentence))
  =
    verifySymbolAliasSentence
        (resolveMetaSort indexedModule)
        attributesVerification
        aliasSentence
verifySentence
    indexedModule
    attributesVerification
    (ObjectSentence (SentenceAliasSentence aliasSentence))
  =
    verifySymbolAliasSentence
        (resolveObjectSort indexedModule)
        attributesVerification
        aliasSentence
verifySentence
    indexedModule
    attributesVerification
    (MetaSentence (SentenceSymbolSentence symbolSentence))
  =
    verifySymbolAliasSentence
        (resolveMetaSort indexedModule)
        attributesVerification
        symbolSentence
verifySentence
    indexedModule
    attributesVerification
    (ObjectSentence (SentenceSymbolSentence symbolSentence))
  =
    verifySymbolAliasSentence
        (resolveObjectSort indexedModule)
        attributesVerification
        symbolSentence
verifySentence
    indexedModule
    attributesVerification
    (MetaSentence (SentenceAxiomSentence axiomSentence))
  =
    verifyAxiomSentence axiomSentence indexedModule attributesVerification
verifySentence
    _
    attributesVerification
    (ObjectSentence (SentenceSortSentence sortSentence))
  =
    verifySortSentence sortSentence attributesVerification
verifySentence _ _ (MetaSentence (SentenceImportSentence _)) =
    -- Since we have an IndexedModule, we assume that imports were already
    -- resolved, so there is nothing left to verify here.
    verifySuccess

verifySymbolAliasSentence
    :: (MetaOrObject level, SentenceSymbolOrAlias ssa)
    => (Id level -> Either (Error VerifyError) (SortDescription level))
    -> AttributesVerification
    -> ssa level FixedPattern Variable
    -> Either (Error VerifyError) VerifySuccess
verifySymbolAliasSentence
    findSortDeclaration attributesVerification sentence
  =
    withContext
        (  getSentenceSymbolOrAliasSentenceName sentence
        ++ " '"
        ++ getId (getSentenceSymbolOrAliasConstructor sentence)
        ++ "' declaration"
        )
        (do
            variables <- buildDeclaredSortVariables sortParams
            mapM_
                (verifySort findSortDeclaration variables)
                (getSentenceSymbolOrAliasArgumentSorts sentence)
            verifySort
                findSortDeclaration
                variables
                (getSentenceSymbolOrAliasResultSort sentence)
            verifyAttributes
                (getSentenceSymbolOrAliasAttributes sentence)
                attributesVerification
        )
  where
    sortParams = getSentenceSymbolOrAliasSortParams sentence

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
    withContext
        ("sort '" ++ getId (sentenceSortName sentenceSort) ++ "' declaration")
        (do
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
    koreFailWhen (unifiedVariable `Set.member` variables)
                (  "Duplicated sort variable: '"
                ++ extractVariableName unifiedVariable
                ++ "'.")
    return (Set.insert unifiedVariable variables)
  where
    extractVariableName (ObjectSortVariable variable) =
        getId (getSortVariable variable)
    extractVariableName (MetaSortVariable variable) =
        getId (getSortVariable variable)
