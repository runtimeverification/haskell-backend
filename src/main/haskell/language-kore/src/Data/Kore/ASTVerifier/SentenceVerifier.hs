module Data.Kore.ASTVerifier.SentenceVerifier
    (verifyUniqueNames, verifySentences) where

import           Control.Monad (foldM)
import           Data.Kore.AST
import           Data.Kore.ASTVerifier.AttributesVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.ASTVerifier.SortVerifier
import           Data.Kore.Error
import           Data.Maybe (mapMaybe)
import qualified Data.Set as Set

verifyUniqueNames
    :: [Sentence]
    -> Set.Set String
    -> Either (Error VerifyError) (Set.Set String)
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
definedNameForSentence (SentenceAxiomSentence _) = Nothing

verifySentences
    :: (Id Object -> Either (Error VerifyError) (SortDescription Object))
    -> (Id Meta -> Either (Error VerifyError) (SortDescription Meta))
    -> IndexedModule
    -> [Sentence]
    -> Either (Error VerifyError) VerifySuccess
verifySentences
    findObjectSortDeclaration findMetaSortDeclaration indexedModule sentences
  = do
    mapM_
        (verifySentence
            findObjectSortDeclaration findMetaSortDeclaration indexedModule)
        sentences
    verifySuccess

verifySentence
    :: (Id Object -> Either (Error VerifyError) (SortDescription Object))
    -> (Id Meta -> Either (Error VerifyError) (SortDescription Meta))
    -> IndexedModule
    -> Sentence
    -> Either (Error VerifyError) VerifySuccess
verifySentence
    _
    findMetaSortDeclaration
    indexedModule
    (MetaSentenceAliasSentence aliasSentence)
  =
    verifySymbolAliasSentence
        findMetaSortDeclaration indexedModule aliasSentence
verifySentence
    findObjectSortDeclaration
    _
    indexedModule
    (ObjectSentenceAliasSentence aliasSentence)
  =
    verifySymbolAliasSentence
        findObjectSortDeclaration indexedModule aliasSentence
verifySentence
    _
    findMetaSortDeclaration
    indexedModule
    (MetaSentenceSymbolSentence symbolSentence)
  =
    verifySymbolAliasSentence
        findMetaSortDeclaration indexedModule symbolSentence
verifySentence
    findObjectSortDeclaration
    _
    indexedModule
    (ObjectSentenceSymbolSentence symbolSentence)
  =
    verifySymbolAliasSentence
        findObjectSortDeclaration indexedModule symbolSentence
verifySentence _ _ indexedModule (SentenceAxiomSentence axiomSentence) =
    verifyAxiomSentence axiomSentence indexedModule
verifySentence _ _ indexedModule (SentenceSortSentence sortSentence) =
    verifySortSentence sortSentence indexedModule


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
                (verifySortUsage findSortDeclaration variables)
                (getSentenceSymbolOrAliasArgumentSorts sentence)
            verifySortUsage
                findSortDeclaration
                variables
                (getSentenceSymbolOrAliasReturnSort sentence)
            verifyAttributes
                (getSentenceSymbolOrAliasAttributes sentence)
                indexedModule
                (Set.fromList (map asUnifiedSortVariable sortParams))
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
