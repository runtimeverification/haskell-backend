module Data.Kore.MetaML.ASTGen where

import           Data.Fix
import           Test.QuickCheck.Gen  (Gen, oneof, scale)

import           Data.Kore.AST
import           Data.Kore.ASTGen
import           Data.Kore.MetaML.AST

metaMLPatternGen :: Gen (MetaMLPattern Variable)
metaMLPatternGen = Fix <$> patternGen metaMLPatternGen Meta

metaSentenceAxiomGen :: Gen MetaSentenceAxiom
metaSentenceAxiomGen = pure MetaSentenceAxiom
    <*> couple (scale (`div` 2) (sortVariableGen Meta))
    <*> scale (`div` 2) metaMLPatternGen
    <*> scale (`div` 2) attributesGen

metaSentenceGen :: Gen MetaSentence
metaSentenceGen = oneof
    [ AliasMetaSentence <$> sentenceAliasGen Meta
    , SymbolMetaSentence <$> sentenceSymbolGen Meta
    , ImportMetaSentence <$> sentenceImportGen
    , AxiomMetaSentence <$> metaSentenceAxiomGen
    ]

metaModuleGen :: Gen MetaModule
metaModuleGen = pure MetaModule
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) metaSentenceGen)
    <*> scale (`div` 2) attributesGen
