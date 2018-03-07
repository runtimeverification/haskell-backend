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
import           Data.Kore.AST
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.ASTVerifier.Resolvers
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Maybe                               (mapMaybe)
import qualified Data.Set                                 as Set

{-|'verifyUniqueNames' verifies that names defined in a list of sentences are
unique both within the list and outside, using the provided name set.
-}
verifyUniqueNames
    :: [Sentence]
    -> Set.Set String
    -- ^ Names that are already defined.
    -> Either (Error VerifyError) (Set.Set String)
    -- ^ On success returns the names that were previously defined together with
    -- the names defined in the given 'Module'.
verifyUniqueNames sentences existingNames =
    foldM verifyUniqueName existingNames
        (mapMaybe definedNameForSentence sentences)

verifyUniqueName
    :: Set.Set String
    -> String
    -> Either (Error VerifyError) (Set.Set String)
verifyUniqueName set name =
    if name `Set.member` set
        then koreFail ("Duplicated name: '" ++ name ++ "'.")
        else Right (Set.insert name set)

definedNameForSentence :: Sentence -> Maybe String
definedNameForSentence (MetaSentenceAliasSentence sentenceAlias) =
    Just (getId (getSentenceSymbolOrAliasConstructor sentenceAlias))
definedNameForSentence (ObjectSentenceAliasSentence sentenceAlias) =
    Just (getId (getSentenceSymbolOrAliasConstructor sentenceAlias))
definedNameForSentence (MetaSentenceSymbolSentence sentenceSymbol) =
    Just (getId (getSentenceSymbolOrAliasConstructor sentenceSymbol))
definedNameForSentence (ObjectSentenceSymbolSentence sentenceSymbol) =
    Just (getId (getSentenceSymbolOrAliasConstructor sentenceSymbol))
definedNameForSentence (SentenceSortSentence sentenceSort) =
    Just (getId (sentenceSortName sentenceSort))
definedNameForSentence (SentenceImportSentence _) = Nothing
definedNameForSentence (SentenceAxiomSentence _) = Nothing

{-|'verifySentences' verifies the welformedness of a list of Kore 'Sentence's.
-}
verifySentences
    :: IndexedModule
    -- ^ The module containing all definitions which are visible in this
    -- pattern.
    -> [Sentence]
    -> Either (Error VerifyError) VerifySuccess
verifySentences
    indexedModule sentences
  = do
    mapM_ (verifySentence indexedModule) sentences
    verifySuccess

verifySentence
    :: IndexedModule
    -> Sentence
    -> Either (Error VerifyError) VerifySuccess
verifySentence
    indexedModule
    (MetaSentenceAliasSentence aliasSentence)
  =
    verifySymbolAliasSentence
        (resolveMetaSort indexedModule) indexedModule aliasSentence
verifySentence
    indexedModule
    (ObjectSentenceAliasSentence aliasSentence)
  =
    verifySymbolAliasSentence
        (resolveObjectSort indexedModule) indexedModule aliasSentence
verifySentence
    indexedModule
    (MetaSentenceSymbolSentence symbolSentence)
  =
    verifySymbolAliasSentence
        (resolveMetaSort indexedModule) indexedModule symbolSentence
verifySentence
    indexedModule
    (ObjectSentenceSymbolSentence symbolSentence)
  =
    verifySymbolAliasSentence
        (resolveObjectSort indexedModule) indexedModule symbolSentence
verifySentence indexedModule (SentenceAxiomSentence axiomSentence) =
    verifyAxiomSentence axiomSentence indexedModule
verifySentence indexedModule (SentenceSortSentence sortSentence) =
    verifySortSentence sortSentence indexedModule
verifySentence _ (SentenceImportSentence _) =
    -- Since we have an IndexedModule, we assume that imports were already
    -- resolved, so there is nothing left to verify here.
    verifySuccess

verifySymbolAliasSentence
    :: (IsMeta a, SentenceSymbolOrAlias ssa)
    => (Id a -> Either (Error VerifyError) (SortDescription a))
    -> IndexedModule
    -> ssa a
    -> Either (Error VerifyError) VerifySuccess
verifySymbolAliasSentence
    findSortDeclaration indexedModule sentence
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
                indexedModule
                variables
        )
  where
    sortParams = getSentenceSymbolOrAliasSortParams sentence

verifyAxiomSentence
    :: SentenceAxiom
    -> IndexedModule
    -> Either (Error VerifyError) VerifySuccess
verifyAxiomSentence axiom indexedModule =
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
                (sentenceAxiomAttributes axiom) indexedModule variables
        )

verifySortSentence
    :: SentenceSort -> IndexedModule -> Either (Error VerifyError) VerifySuccess
verifySortSentence sentenceSort indexedModule =
    withContext
        ("sort '" ++ getId (sentenceSortName sentenceSort) ++ "' declaration")
        (do
            variables <-
                buildDeclaredSortVariables (sentenceSortParameters sentenceSort)
            verifyAttributes
                (sentenceSortAttributes sentenceSort) indexedModule variables
        )

buildDeclaredSortVariables
    :: IsMeta a
    => [SortVariable a]
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
