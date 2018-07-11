module Data.Kore.MetaML.ASTGen where

import           Data.Fix
import           Test.QuickCheck.Gen        (Gen, frequency, oneof, sized)

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTGen
import           Data.Kore.MetaML.AST

metaMLPatternGen :: Gen (MetaMLPattern Variable)
metaMLPatternGen = Fix <$> sized (\n ->
    if n<=0
        then oneof
            [ StringLiteralPattern <$> stringLiteralGen
            , CharLiteralPattern <$> charLiteralGen
            ]
        else frequency
            [ (15, patternGen metaMLPatternGen Meta)
            , (1, StringLiteralPattern <$> stringLiteralGen)
            , (1, CharLiteralPattern <$> charLiteralGen)
            ]
    )

metaSentenceGen :: Gen MetaSentence
metaSentenceGen = oneof
    [ (SentenceSymbolSentence <$> sentenceSymbolGen Meta)
    , (SentenceAliasSentence <$> sentenceAliasGen Meta metaMLPatternGen)
    , (SentenceImportSentence
          <$> sentenceImportGen)
    , (SentenceAxiomSentence
          <$> sentenceAxiomGen (sortVariableGen Meta) metaMLPatternGen)
    ]

metaModuleGen :: Gen MetaModule
metaModuleGen = moduleGen metaSentenceGen
