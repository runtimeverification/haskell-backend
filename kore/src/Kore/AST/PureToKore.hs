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
    , sentencePureToKore
    , axiomSentencePureToKore
    , modulePureToKore
    , definitionPureToKore
    , patternKoreToPure
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import qualified Data.Functor.Foldable as Recursive

import Kore.AST.Kore
import Kore.AST.Pure
import Kore.AST.Sentence
import Kore.Error

patternPureToKore
    :: (Functor domain, MetaOrObject level)
    => PurePattern level domain variable (annotation level)
    -> KorePattern domain variable (Unified annotation)
patternPureToKore =
    Recursive.unfold patternPureToKoreWorker
  where
    patternPureToKoreWorker (Recursive.project -> ann :< pat) =
        asUnified ann :< asUnifiedPattern pat

-- |Given a level, this function attempts to extract a pure patten
-- of this level from a KorePattern.
-- Note that this function does not lift the term, but rather fails with
-- 'error' any part of the pattern if of a different level.
-- For lifting functions see "Kore.MetaML.Lift".
patternKoreToPure
    :: (MetaOrObject level, Traversable domain)
    => level
    -> KorePattern domain variable (Unified annotation)
    -> Either (Error a) (PurePattern level domain variable (annotation level))
patternKoreToPure level =
    Recursive.fold (extractPurePattern $ isMetaOrObject $ toProxy level)

extractPurePattern
    ::  ( MetaOrObject level
        , Traversable domain
        , result ~ PurePattern level domain variable (annotation level)
        )
    => IsMetaOrObject level
    -> Base
        (KorePattern domain variable (Unified annotation))
        (Either (Error e) result)
    -> Either (Error e) result
extractPurePattern IsObject = \(ann :< pat) ->
    case pat of
        UnifiedObjectPattern opat ->
            case ann of
                UnifiedObject oann ->
                    Recursive.embed . (oann :<) <$> sequence opat

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
