module Data.Kore.MetaML.MetaToKore where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.MetaML.AST

import           Data.Fix

patternMetaToKore :: CommonMetaPattern -> UnifiedPattern
patternMetaToKore = cata MetaPattern

attributesMetaToKore :: MetaAttributes -> Attributes
attributesMetaToKore ma =
    Attributes (map patternMetaToKore (getMetaAttributes ma))

sentenceMetaToKore :: MetaSentence -> Sentence
sentenceMetaToKore (AliasMetaSentence msa) = asSentence msa
    { sentenceAliasAttributes =
          attributesMetaToKore (sentenceAliasAttributes msa)
    }

moduleMetaToKore :: MetaModule -> Module
moduleMetaToKore mm = Module
    { moduleName = metaModuleName mm
    , moduleSentences = map sentenceMetaToKore (metaModuleSentences mm)
    , moduleAttributes = attributesMetaToKore (metaModuleAttributes mm)
    }

definitionMetaToKore :: MetaDefinition -> Definition
definitionMetaToKore dm = Definition
    { definitionAttributes = attributesMetaToKore (metaDefinitionAttributes dm)
    , definitionModules = map moduleMetaToKore (metaDefinitionModules dm)
    }
