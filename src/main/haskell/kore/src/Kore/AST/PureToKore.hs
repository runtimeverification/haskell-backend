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

import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error

patternPureToKore
    :: (Functor dom, MetaOrObject level)
    => PurePattern level dom var ann
    -> KorePattern dom var ann
patternPureToKore =
    Recursive.unfold patternPureToKoreWorker
  where
    patternPureToKoreWorker (Recursive.project -> ann :< pat) =
        ann :< asUnifiedPattern pat

-- |Given a level, this function attempts to extract a pure patten
-- of this level from a KorePattern.
-- Note that this function does not lift the term, but rather fails with
-- 'error' any part of the pattern if of a different level.
-- For lifting functions see "Kore.MetaML.Lift".
patternKoreToPure
    :: MetaOrObject level
    => level
    -> CommonKorePattern
    -> Either (Error a) (CommonPurePattern level Domain.Builtin ())
patternKoreToPure level =
    Recursive.fold (extractPurePattern $ isMetaOrObject $ toProxy level)

extractPurePattern
    ::  ( MetaOrObject level
        , result ~ Either (Error a) (CommonPurePattern level Domain.Builtin ())
        )
    => IsMetaOrObject level
    -> Base CommonKorePattern result
    -> result
extractPurePattern IsMeta = \(_ :< pat) ->
    case pat of
        UnifiedMetaPattern meta ->
            Recursive.embed . (mempty :<) <$> sequence meta
        UnifiedObjectPattern _ ->
            koreFail "Unexpected object-level pattern"
extractPurePattern IsObject = \(_ :< pat) ->
    case pat of
        UnifiedObjectPattern object ->
            Recursive.embed . (mempty :<) <$> sequence object
        UnifiedMetaPattern _ ->
            koreFail "Unexpected meta-level pattern"

-- FIXME : all of this attribute record syntax stuff
-- Should be temporary measure
sentencePureToKore
    :: (Functor dom, MetaOrObject level)
    => Sentence level (SortVariable level) (PurePattern level dom var ann)
    -> UnifiedSentence UnifiedSortVariable (KorePattern dom var ann)
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
    :: (Functor dom, MetaOrObject level)
    => SentenceAlias level (PurePattern level dom var ann)
    -> SentenceAlias level (KorePattern dom var ann)
aliasSentencePureToKore = (<$>) patternPureToKore

axiomSentencePureToKore
    :: (Functor dom, MetaOrObject level)
    => SentenceAxiom (SortVariable level) (PurePattern level dom var ann)
    -> SentenceAxiom UnifiedSortVariable (KorePattern dom var ann)
axiomSentencePureToKore = unifyAxiomParameters . (<$>) patternPureToKore
  where
    unifyAxiomParameters axiom@SentenceAxiom { sentenceAxiomParameters } =
        axiom
            { sentenceAxiomParameters =
                asUnified <$> sentenceAxiomParameters
            }

modulePureToKore
    :: MetaOrObject level
    => PureModule level Domain.Builtin
    -> KoreModule
modulePureToKore mm = Module
    { moduleName = moduleName mm
    , moduleSentences = map sentencePureToKore (moduleSentences mm)
    , moduleAttributes =  moduleAttributes mm
    }

definitionPureToKore
    :: MetaOrObject level
    => PureDefinition level Domain.Builtin
    -> KoreDefinition
definitionPureToKore dm = Definition
    { definitionAttributes = definitionAttributes dm
    , definitionModules = map modulePureToKore (definitionModules dm)
    }
