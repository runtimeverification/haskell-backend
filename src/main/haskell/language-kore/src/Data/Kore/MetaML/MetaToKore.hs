{-|
Module      : Data.Kore.MetaML.MetaToKore
Description : Functionality for viewing 'Meta'-only as unified Kore constructs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

The name of the functions defined below are self-explanatory. They link
'Meta' structures from 'Data.Kore.MetaML.AST' to their Kore counterparts in
'Data.Kore.AST.Kore'

-}
module Data.Kore.MetaML.MetaToKore where

import           Data.Kore.AST.Common (Attributes (..), Definition (..),
                                       Module (..), SentenceAlias (..),
                                       SentenceAxiom (..), SentenceImport (..),
                                       SentenceSymbol (..), asSentence)
import           Data.Kore.AST.Kore
import           Data.Kore.MetaML.AST

import           Data.Fix

patternMetaToKore :: CommonMetaPattern -> UnifiedPattern
patternMetaToKore = cata MetaPattern

attributesMetaToKore :: MetaAttributes -> KoreAttributes
attributesMetaToKore ma =
    Attributes (map patternMetaToKore (getAttributes ma))

sentenceMetaToKore :: MetaSentence -> Sentence
sentenceMetaToKore (AliasMetaSentence msa) = asSentence msa
    { sentenceAliasAttributes =
        attributesMetaToKore (sentenceAliasAttributes msa)
    }
sentenceMetaToKore (SymbolMetaSentence mss) = asSentence mss
    { sentenceSymbolAttributes =
        attributesMetaToKore (sentenceSymbolAttributes mss)
    }
sentenceMetaToKore (ImportMetaSentence msi) = asSentence msi
    { sentenceImportAttributes =
        attributesMetaToKore (sentenceImportAttributes msi)
    }
sentenceMetaToKore (AxiomMetaSentence msx) = asSentence SentenceAxiom
    { sentenceAxiomAttributes =
        attributesMetaToKore (sentenceAxiomAttributes msx)
    , sentenceAxiomPattern =
        patternMetaToKore (sentenceAxiomPattern msx)
    , sentenceAxiomParameters =
        map MetaSortVariable (sentenceAxiomParameters msx)
    }

moduleMetaToKore :: MetaModule -> KoreModule
moduleMetaToKore mm = Module
    { moduleName = moduleName mm
    , moduleSentences = map sentenceMetaToKore (moduleSentences mm)
    , moduleAttributes = attributesMetaToKore (moduleAttributes mm)
    }

definitionMetaToKore :: MetaDefinition -> KoreDefinition
definitionMetaToKore dm = Definition
    { definitionAttributes = attributesMetaToKore (definitionAttributes dm)
    , definitionModules = map moduleMetaToKore (definitionModules dm)
    }
