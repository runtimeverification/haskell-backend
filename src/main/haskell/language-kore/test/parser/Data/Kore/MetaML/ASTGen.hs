module Data.Kore.MetaML.ASTGen where

import           Data.Fix
import           Test.QuickCheck.Gen  (Gen, oneof, scale)

import           Data.Kore.AST.Common
import           Data.Kore.ASTGen
import           Data.Kore.MetaML.AST

metaMLPatternGen :: Gen CommonMetaPattern
metaMLPatternGen = Fix <$> patternGen metaMLPatternGen Meta

metaAttributesGen :: Gen MetaAttributes
metaAttributesGen = attributesGen (SentenceMetaPattern <$> metaMLPatternGen)

metaSentenceGen :: Gen MetaSentence
metaSentenceGen = sentenceGen
    [ AliasMetaSentence <$> sentenceAliasGen metaMLPatternGen Meta
    , SymbolMetaSentence <$> sentenceSymbolGen metaMLPatternGen Meta
    , ImportMetaSentence <$> sentenceImportGen metaMLPatternGen
    , AxiomMetaSentence <$> metaSentenceAxiomGen
    ]

metaModuleGen :: Gen MetaModule
metaModuleGen = pure Module
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) metaSentenceGen)
    <*> scale (`div` 2) metaAttributesGen
