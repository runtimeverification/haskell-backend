{-|
Module      : Kore.AST.PureToKore
Description : Functionality for viewing "Pure"-only as unified Kore constructs.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

The name of the functions defined below are self-explanatory. They link @Pure@
structures from "Kore.AST.PureML" to their @Kore@ counterparts in
"Kore.AST.Kore"

-}
module Kore.AST.PureToKore
    ( patternPureToKore
    , patternKoreToPure
    , sentencePureToKore
    , sentenceKoreToPure
    , axiomSentencePureToKore
    , modulePureToKore
    , definitionPureToKore
    , annotationKoreToPure
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import qualified Data.Functor.Foldable as Recursive

import qualified Kore.Annotation.Valid as Valid
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import qualified Kore.Domain.Builtin as Domain

patternPureToKore
    :: (Functor domain, MetaOrObject level)
    => PurePattern level domain variable (annotation level)
    -> KorePattern domain variable (Unified annotation)
patternPureToKore =
    Recursive.unfold patternPureToKoreWorker
  where
    patternPureToKoreWorker (Recursive.project -> ann :< pat) =
        asUnified ann :< asUnifiedPattern pat

{- | Unwrap a 'KorePattern'.

For historical reasons, the parser produces a 'KorePattern' but most code
operates on 'PurePattern'.

 -}
-- TODO (thomas.tuegel): Remove the distinction between KorePattern and
-- PurePattern.
patternKoreToPure
    :: Traversable domain
    => KorePattern domain Variable (Unified annotation)
    -> PurePattern Object domain Variable (annotation Object)
patternKoreToPure = Recursive.fold extractPurePattern

extractPurePattern
    ::  ( MetaOrObject level
        , Traversable domain
        , result ~ PurePattern level domain variable (annotation level)
        )
    => Base (KorePattern domain variable (Unified annotation)) result
    -> result
extractPurePattern (UnifiedObject oann :< UnifiedObjectPattern opat) =
    Recursive.embed (oann :< opat)

annotationKoreToPure
    :: Functor f
    => f (Valid (Unified Variable) Object)
    -> f (Valid (Variable Object) Object)
annotationKoreToPure = fmap (Valid.mapVariables fromUnified)

{- | Unwrap a 'UnifiedSentence'.

For historical reasons, the parser produces a 'UnifiedSentence' but most code
operates on 'Sentence'.

 -}
-- TODO (thomas.tuegel): Remove the distinction between UnifiedSentence and
-- Sentence.
sentenceKoreToPure
    :: UnifiedSentence UnifiedSortVariable VerifiedKorePattern
    -> Sentence Object (SortVariable Object) (VerifiedPurePattern Object Domain.Builtin)
sentenceKoreToPure (UnifiedObjectSentence sentence) =
    case annotationKoreToPure . patternKoreToPure <$> sentence of
        SentenceAliasSentence sentenceAlias ->
            SentenceAliasSentence sentenceAlias
        SentenceSymbolSentence sentenceSymbol ->
            SentenceSymbolSentence sentenceSymbol
        SentenceImportSentence sentenceImport ->
            SentenceImportSentence sentenceImport
        SentenceSortSentence sentenceSort ->
            SentenceSortSentence sentenceSort
        SentenceHookSentence sentenceHook ->
            SentenceHookSentence sentenceHook
        SentenceAxiomSentence sentenceAxiom ->
            SentenceAxiomSentence
            $ sentenceKoreAxiomToPure sentenceAxiom
        SentenceClaimSentence sentenceClaim ->
            SentenceClaimSentence
            $ sentenceKoreAxiomToPure sentenceClaim

sentenceKoreAxiomToPure
    :: SentenceAxiom UnifiedSortVariable patternType
    -> SentenceAxiom (SortVariable Object) patternType
sentenceKoreAxiomToPure sentenceAxiom =
    sentenceAxiom
        { sentenceAxiomParameters =
            sortVariableKoreToPure <$> sentenceAxiomParameters sentenceAxiom
        }

sortVariableKoreToPure
    :: UnifiedSortVariable -> SortVariable Object
sortVariableKoreToPure (UnifiedObject var) = var

-- FIXME : all of this attribute record syntax stuff
-- Should be temporary measure
sentencePureToKore
    :: (Functor domain, MetaOrObject level)
    => Sentence level (SortVariable level)
        (PurePattern level domain variable (annotation level))
    -> UnifiedSentence UnifiedSortVariable
        (KorePattern domain variable (Unified annotation))
sentencePureToKore (SentenceAliasSentence sa) =
    asSentence $ aliasSentencePureToKore sa
sentencePureToKore (SentenceSymbolSentence (SentenceSymbol a b c d)) =
    constructUnifiedSentence SentenceSymbolSentence $ SentenceSymbol a b c d
sentencePureToKore (SentenceImportSentence (SentenceImport a b)) =
    constructUnifiedSentence SentenceImportSentence $ SentenceImport a b
sentencePureToKore (SentenceAxiomSentence msx) =
    asKoreAxiomSentence $ axiomSentencePureToKore msx
sentencePureToKore (SentenceClaimSentence msx) =
    asKoreClaimSentence $ axiomSentencePureToKore msx
sentencePureToKore (SentenceSortSentence mss) =
  constructUnifiedSentence SentenceSortSentence mss
    { sentenceSortName = sentenceSortName mss
    , sentenceSortParameters = sentenceSortParameters mss
    }
sentencePureToKore (SentenceHookSentence (SentenceHookedSort mss)) =
  constructUnifiedSentence (SentenceHookSentence . SentenceHookedSort) mss
    { sentenceSortName = sentenceSortName mss
    , sentenceSortParameters = sentenceSortParameters mss
    }
sentencePureToKore (SentenceHookSentence (SentenceHookedSymbol (SentenceSymbol a b c d))) =
    constructUnifiedSentence (SentenceHookSentence . SentenceHookedSymbol) $ SentenceSymbol a b c d

aliasSentencePureToKore
    :: (Functor domain, MetaOrObject level)
    => SentenceAlias level
        (PurePattern level domain variable (annotation level))
    -> SentenceAlias level (KorePattern domain variable (Unified annotation))
aliasSentencePureToKore = (<$>) patternPureToKore

axiomSentencePureToKore
    :: (Functor domain, MetaOrObject level)
    => SentenceAxiom (SortVariable level)
        (PurePattern level domain variable (annotation level))
    -> SentenceAxiom UnifiedSortVariable
        (KorePattern domain variable (Unified annotation))
axiomSentencePureToKore = unifyAxiomParameters . (<$>) patternPureToKore
  where
    unifyAxiomParameters axiom@SentenceAxiom { sentenceAxiomParameters } =
        axiom
            { sentenceAxiomParameters =
                asUnified <$> sentenceAxiomParameters
            }

modulePureToKore
    ::  ( MetaOrObject level
        , Functor domain
        , purePattern ~ PurePattern level domain variable (annotation level)
        , korePattern ~ KorePattern domain variable (Unified annotation)
        )
    => Module (Sentence level (SortVariable level) purePattern)
    -> Module (UnifiedSentence UnifiedSortVariable korePattern)
modulePureToKore mm = Module
    { moduleName = moduleName mm
    , moduleSentences = map sentencePureToKore (moduleSentences mm)
    , moduleAttributes =  moduleAttributes mm
    }

definitionPureToKore
    ::  ( MetaOrObject level
        , Functor domain
        , purePattern ~ PurePattern level domain variable (annotation level)
        , korePattern ~ KorePattern domain variable (Unified annotation)
        )
    => Definition (Sentence level (SortVariable level) purePattern)
    -> Definition (UnifiedSentence UnifiedSortVariable korePattern)
definitionPureToKore dm = Definition
    { definitionAttributes = definitionAttributes dm
    , definitionModules = map modulePureToKore (definitionModules dm)
    }
