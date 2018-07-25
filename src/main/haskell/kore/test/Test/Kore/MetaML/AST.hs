module Test.Kore.MetaML.AST where

import Test.QuickCheck.Gen
       ( Gen, frequency, oneof, sized )

import Data.Functor.Foldable

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.MetaML.AST

import Test.Kore

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
