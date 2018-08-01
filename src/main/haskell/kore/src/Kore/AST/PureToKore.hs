{-|
Module      : Kore.AST.PureToKore
Description : Functionality for viewing "Pure"-only as unified Kore constructs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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

import Data.Functor.Foldable

import Data.Functor.Impredicative
       ( Rotate31 (..) )
import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.Sentence
import Kore.ASTTraversals
import Kore.Error

patternPureToKore
    :: MetaOrObject level => CommonPurePattern level -> CommonKorePattern
patternPureToKore = cata asKorePattern

-- |Given a level, this function attempts to extract a pure patten
-- of this level from a KorePattern.
-- Note that this function does not lift the term, but rather fails with
-- 'error' any part of the pattern if of a different level.
-- For lifting functions see "Kore.MetaML.Lift".
patternKoreToPure
    :: MetaOrObject level
    => level
    -> CommonKorePattern
    -> Either (Error a) (CommonPurePattern level)
patternKoreToPure level = patternBottomUpVisitorM (extractPurePattern level)

extractPurePattern
    :: (MetaOrObject level, MetaOrObject level1)
    => level
    -> Pattern level1 Variable (CommonPurePattern level)
    -> Either (Error a) (CommonPurePattern level)
extractPurePattern level p =
    case (isMetaOrObject (Rotate31 p), isMetaOrObject (toProxy level)) of
        (IsMeta, IsMeta) -> return (Fix p)
        (IsObject, IsObject) -> return (Fix p)
        _ -> koreFail ("Unexpected non-" ++ show level ++ " pattern")

-- FIXME : all of this attribute record syntax stuff
-- Should be temporary measure
sentencePureToKore
    :: MetaOrObject level => PureSentence level -> KoreSentence
sentencePureToKore (SentenceAliasSentence sa) =
    asSentence $ aliasSentencePureToKore sa
sentencePureToKore (SentenceSymbolSentence (SentenceSymbol a b c d)) =
    constructUnifiedSentence SentenceSymbolSentence $ SentenceSymbol a b c d
sentencePureToKore (SentenceImportSentence (SentenceImport a b)) =
    constructUnifiedSentence SentenceImportSentence $ SentenceImport a b
sentencePureToKore (SentenceAxiomSentence msx) =
    asSentence (axiomSentencePureToKore msx)
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
    :: MetaOrObject level
    => PureSentenceAlias level
    -> KoreSentenceAlias level
aliasSentencePureToKore msx = msx
    { sentenceAliasLeftPattern =
        patternPureToKore <$> sentenceAliasLeftPattern msx
    , sentenceAliasRightPattern =
        patternPureToKore <$> sentenceAliasRightPattern msx
    }

axiomSentencePureToKore
    :: MetaOrObject level
    => PureSentenceAxiom level
    -> KoreSentenceAxiom
axiomSentencePureToKore msx = msx
    { sentenceAxiomPattern =
        patternPureToKore (sentenceAxiomPattern msx)
    , sentenceAxiomParameters =
        map asUnified (sentenceAxiomParameters msx)
    }

modulePureToKore
    :: MetaOrObject level => PureModule level -> KoreModule
modulePureToKore mm = Module
    { moduleName = moduleName mm
    , moduleSentences = map sentencePureToKore (moduleSentences mm)
    , moduleAttributes =  moduleAttributes mm
    }

definitionPureToKore
    :: MetaOrObject level => PureDefinition level -> KoreDefinition
definitionPureToKore dm = Definition
    { definitionAttributes = definitionAttributes dm
    , definitionModules = map modulePureToKore (definitionModules dm)
    }
