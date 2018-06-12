{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.AST.PureToKore
Description : Functionality for viewing "Pure"-only as unified Kore constructs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

The name of the functions defined below are self-explanatory. They link
"Pure" structures from 'Data.Kore.AST.PureML' to their "Kore" counterparts in
'Data.Kore.AST.Kore'

-}
module Data.Kore.AST.PureToKore
    ( patternPureToKore
    , attributesPureToKore
    , sentencePureToKore
    , modulePureToKore
    , definitionPureToKore
    , patternKoreToPure
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.ASTTraversals
import           Data.Kore.HaskellExtensions (Rotate31 (..))

import           Data.Fix

patternPureToKore
    :: MetaOrObject level => CommonPurePattern level -> CommonKorePattern
patternPureToKore = cata asKorePattern

-- |Given a level, this function attempts to extract a pure patten
-- of this level from a KorePattern.
-- Note that this function does not lift the term, but rather fails with
-- 'error' any part of the pattern if of a different level.
-- For lifting functions see 'Data.Kore.MetaML.Lift'.
patternKoreToPure
    :: MetaOrObject level
    => level -> CommonKorePattern -> CommonPurePattern level
patternKoreToPure level = patternBottomUpVisitor (extractPurePattern level)

extractPurePattern
    :: (MetaOrObject level, MetaOrObject level1)
    => level
    -> Pattern level1 Variable (CommonPurePattern level)
    -> CommonPurePattern level
extractPurePattern level p =
  case (isMetaOrObject (Rotate31 p), isMetaOrObject (toProxy level)) of
    (IsMeta, IsMeta) -> Fix p
    (IsObject, IsObject) -> Fix p
    _ -> error ("Undexpected non-" ++ show level ++ " pattern")

attributesPureToKore
    :: MetaOrObject level => PureAttributes level -> KoreAttributes
attributesPureToKore ma =
    Attributes (map patternPureToKore (getAttributes ma))

sentencePureToKore
    :: MetaOrObject level => PureSentence level -> KoreSentence
sentencePureToKore (SentenceAliasSentence msa) = asSentence msa
    { sentenceAliasAttributes =
        attributesPureToKore (sentenceAliasAttributes msa)
    , sentenceAliasLeftPattern = patternPureToKore <$> sentenceAliasLeftPattern msa
    , sentenceAliasRightPattern = patternPureToKore <$> sentenceAliasRightPattern msa
    }
sentencePureToKore (SentenceSymbolSentence mss) = asSentence mss
    { sentenceSymbolAttributes =
        attributesPureToKore (sentenceSymbolAttributes mss)
    }
sentencePureToKore (SentenceImportSentence msi) = asSentence msi
    { sentenceImportAttributes =
        attributesPureToKore (sentenceImportAttributes msi)
    }
sentencePureToKore (SentenceAxiomSentence msx) = asSentence SentenceAxiom
    { sentenceAxiomAttributes =
        attributesPureToKore (sentenceAxiomAttributes msx)
    , sentenceAxiomPattern =
        patternPureToKore (sentenceAxiomPattern msx)
    , sentenceAxiomParameters =
        map asUnified (sentenceAxiomParameters msx)
    }
sentencePureToKore (SentenceSortSentence mss) = asSentence SentenceSort
    { sentenceSortName = sentenceSortName mss
    , sentenceSortParameters = sentenceSortParameters mss
    , sentenceSortAttributes = attributesPureToKore (sentenceSortAttributes mss)
    }

modulePureToKore
    :: MetaOrObject level => PureModule level -> KoreModule
modulePureToKore mm = Module
    { moduleName = moduleName mm
    , moduleSentences = map sentencePureToKore (moduleSentences mm)
    , moduleAttributes = attributesPureToKore (moduleAttributes mm)
    }

definitionPureToKore
    :: MetaOrObject level => PureDefinition level -> KoreDefinition
definitionPureToKore dm = Definition
    { definitionAttributes = attributesPureToKore (definitionAttributes dm)
    , definitionModules = map modulePureToKore (definitionModules dm)
    }
