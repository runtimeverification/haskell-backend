module Test.Kore.OptionsParser
    ( test_flags
    ) where

import Prelude.Kore

import Data.Maybe
    ( fromJust
    )

import Test.Tasty
import Test.Tasty.HUnit.Ext

import Kore.OptionsParser

import Options.Applicative

test_flags :: [TestTree]
test_flags =
    [ testGroup "print-definition"
        [ testCase "default is False" $ do
            let flag_value = willPrintDefinition $ runParser commandLineParser
                    ["mock/path/to/file"]
            assertEqual "Expected print-definition to be False by default"
                False flag_value
        , testCase "given explicitly is True" $ do
            let flag_value = willPrintDefinition $ runParser commandLineParser
                    ["mock/path/to/file", "--print-definition"]
            assertEqual "Expected --print-definition to give True"
                True flag_value
        , testCase "with `no` prefix is False" $ do
            let flag_value = willPrintDefinition $ runParser commandLineParser
                    ["mock/path/to/file", "--no-print-definition"]
            assertEqual "Expected --no-print-definition to give False"
                False flag_value
        ]
    , testGroup "print-pattern"
        [ testCase "default is False" $ do
            let flag_value = willPrintPattern $ runParser commandLineParser
                    ["mock/path/to/file"]
            assertEqual "Expected print-pattern to be False by default"
                False flag_value
        , testCase "given explicitly is True" $ do
            let flag_value = willPrintPattern $ runParser commandLineParser
                    ["mock/path/to/file", "--print-pattern"]
            assertEqual "Expected --print-pattern to give True"
                True flag_value
        , testCase "with `no` prefix is False" $ do
            let flag_value = willPrintPattern $ runParser commandLineParser
                    ["mock/path/to/file", "--no-print-pattern"]
            assertEqual "Expected --no-print-pattern to give False"
                False flag_value
        ]
    ]

runParser :: Parser a -> [String] -> a
runParser parser input = fromJust $ getParseResult parserResult
  where
    parserInfo = info parser mempty
    parserResult = execParserPure defaultPrefs parserInfo input
