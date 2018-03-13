module Data.Kore.MetaML.ASTGen where

import           Data.Fix
import           Test.QuickCheck.Gen  (Gen, oneof, scale)

import           Data.Kore.AST.Common
import           Data.Kore.ASTGen
import           Data.Kore.MetaML.AST

metaMLPatternGen :: Gen (MetaMLPattern Variable)
metaMLPatternGen = Fix <$> patternGen metaMLPatternGen Meta

metaAttributesGen :: Gen MetaAttributes
metaAttributesGen = MetaAttributes <$> couple (scale (`div` 4) metaMLPatternGen)

metaSentenceAxiomGen :: Gen MetaSentenceAxiom
metaSentenceAxiomGen = pure SentenceAxiom
    <*> couple (scale (`div` 2) (sortVariableGen Meta))
    <*> scale (`div` 2) metaMLPatternGen
    <*> scale (`div` 2) metaAttributesGen

metaSentenceGen :: Gen MetaSentence
metaSentenceGen = oneof
    [ AliasMetaSentence <$> sentenceAliasGen metaAttributesGen Meta
    , SymbolMetaSentence <$> sentenceSymbolGen metaAttributesGen Meta
    , ImportMetaSentence <$> sentenceImportGen metaAttributesGen
    , AxiomMetaSentence <$> metaSentenceAxiomGen
    ]

metaModuleGen :: Gen MetaModule
metaModuleGen = pure MetaModule
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) metaSentenceGen)
    <*> scale (`div` 2) metaAttributesGen
