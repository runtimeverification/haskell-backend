{-|
Module      : Kore.ASTVerifier.SentenceVerifier
Description : Tools for verifying the wellformedness of a Kore 'Sentence'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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

import Kore.AST.Common
import Kore.AST.Error
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.AST.Sentence
import Kore.ASTVerifier.AttributesVerifier
import Kore.ASTVerifier.Error
import Kore.ASTVerifier.PatternVerifier
import Kore.ASTVerifier.SortVerifier
import Kore.Attribute.Parser ( parseAttributes )
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers

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
    :: Sentence Meta sortParam pat domain variable -> [UnparameterizedId]
definedNamesForMetaSentence (SentenceAliasSentence sentenceAlias) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceAlias) ]
definedNamesForMetaSentence (SentenceSymbolSentence sentenceSymbol) =
    [ toUnparameterizedId (getSentenceSymbolOrAliasConstructor sentenceSymbol) ]
definedNamesForMetaSentence (SentenceImportSentence _) = []
definedNamesForMetaSentence (SentenceAxiomSentence _)  = []
definedNamesForMetaSentence (SentenceSortSentence _)   = []

definedNamesForObjectSentence
    :: Sentence Object sortParam pat domain variable -> [UnparameterizedId]
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
    -> Sentence Meta UnifiedSortVariable UnifiedPattern KoreDomain Variable
    -> Either (Error VerifyError) VerifySuccess
verifyMetaSentence
    builtinVerifiers
    indexedModule
    attributesVerification
    (SentenceAliasSentence aliasSentence)
  =
    verifyAliasSentence
        (fmap getIndexedSentence . resolveSort indexedModule)
        builtinVerifiers
        indexedModule
        attributesVerification
        aliasSentence
verifyMetaSentence
    _
    indexedModule
    attributesVerification
    (SentenceSymbolSentence symbolSentence)
  =
    verifySymbolSentence
        (fmap getIndexedSentence . resolveSort indexedModule)
        indexedModule
        attributesVerification
        symbolSentence
verifyMetaSentence
    builtinVerifiers
    indexedModule
    attributesVerification
    (SentenceAxiomSentence axiomSentence)
  =
    verifyAxiomSentence axiomSentence builtinVerifiers indexedModule attributesVerification
verifyMetaSentence
    _
    _indexedModule
    attributesVerification
    (SentenceSortSentence sortSentence)
  = do
    koreFailWithLocationsWhen
        (sortParams /= [])
        [sortId]
        ("Malformed meta sort '" ++ getId sortId ++ "' with non-empty Parameter sorts.")
    verifyAttributes
        (sentenceSortAttributes sortSentence)
        attributesVerification
  where
    sortId     = sentenceSortName sortSentence
    sortParams = sentenceSortParameters sortSentence
verifyMetaSentence _ _ _ (SentenceImportSentence _) =
    -- Since we have an IndexedModule, we assume that imports were already
    -- resolved, so there is nothing left to verify here.
    verifySuccess

verifyObjectSentence
    :: Builtin.Verifiers
    -> KoreIndexedModule atts
    -> AttributesVerification atts
    -> Sentence Object UnifiedSortVariable UnifiedPattern KoreDomain Variable
    -> Either (Error VerifyError) VerifySuccess
verifyObjectSentence
    builtinVerifiers
    indexedModule
    attributesVerification
    (SentenceAliasSentence aliasSentence)
  =
    verifyAliasSentence
        (fmap getIndexedSentence . resolveSort indexedModule)
        builtinVerifiers
        indexedModule
        attributesVerification
        aliasSentence
verifyObjectSentence
    _
    indexedModule
    attributesVerification
    (SentenceSymbolSentence symbolSentence)
  =
    verifySymbolSentence
        (fmap getIndexedSentence . resolveSort indexedModule)
        indexedModule
        attributesVerification
        symbolSentence
verifyObjectSentence
    _
    _
    attributesVerification
    (SentenceSortSentence sortSentence)
  =
    verifySortSentence sortSentence attributesVerification
verifyObjectSentence
    builtinVerifiers
    _
    attributesVerification
    (SentenceHookSentence (SentenceHookedSort sortSentence))
  =
    do
        verifySortSentence sortSentence attributesVerification
        let SentenceSort { sentenceSortAttributes } = sortSentence
        hook <- castError (parseAttributes sentenceSortAttributes)
        Builtin.sortDeclVerifier builtinVerifiers hook sortSentence
        pure (VerifySuccess ())

verifyObjectSentence
    builtinVerifiers
    indexedModule
    attributesVerification
    (SentenceHookSentence (SentenceHookedSymbol symbolSentence))
  =
    do
        verifySymbolSentence
            findSort
            indexedModule
            attributesVerification
            symbolSentence
        let SentenceSymbol { sentenceSymbolAttributes } = symbolSentence
        hook <- castError (parseAttributes sentenceSymbolAttributes)
        Builtin.symbolVerifier builtinVerifiers hook findSort symbolSentence
        pure (VerifySuccess ())
  where
    findSort = fmap getIndexedSentence . resolveSort indexedModule

verifySymbolSentence
    :: (MetaOrObject level)
    => (Id level -> Either (Error VerifyError) (SortDescription level KoreDomain))
    -> KoreIndexedModule atts
    -> AttributesVerification atts
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
    => (Id level -> Either (Error VerifyError) (SortDescription level KoreDomain))
    -> Builtin.Verifiers
    -> KoreIndexedModule atts
    -> AttributesVerification atts
    -> KoreSentenceAlias level
    -> Either (Error VerifyError) VerifySuccess
verifyAliasSentence
    findSortDeclaration builtinVerifiers indexedModule attributesVerification sentence
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
                (Builtin.patternVerifier builtinVerifiers)
                indexedModule
                variables
                (Just $ asUnified leftPatternSort)
                (asKorePattern $ sentenceAliasLeftPattern sentence)
            verifyPattern
                (Builtin.patternVerifier builtinVerifiers)
                indexedModule
                variables
                (Just $ asUnified rightPatternSort)
                (asKorePattern $ sentenceAliasRightPattern sentence)
            verifyAttributes
                (sentenceAliasAttributes sentence)
                attributesVerification
        )
  where
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
    -> AttributesVerification atts
    -> Either (Error VerifyError) VerifySuccess
verifyAxiomSentence axiom builtinVerifiers indexedModule attributesVerification =
    withContext
        "axiom declaration"
        (do
            variables <-
                buildDeclaredUnifiedSortVariables
                    (sentenceAxiomParameters axiom)
            verifyPattern
                (Builtin.patternVerifier builtinVerifiers)
                indexedModule
                variables
                Nothing
                (sentenceAxiomPattern axiom)
            verifyAttributes
                (sentenceAxiomAttributes axiom)
                attributesVerification
        )

verifySortSentence
    :: KoreSentenceSort Object
    -> AttributesVerification atts
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
