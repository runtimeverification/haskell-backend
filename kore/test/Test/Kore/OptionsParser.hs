module Test.Kore.OptionsParser
    ( test_flags
    , test_options
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
                    ["mock/path/to/def"]
            assertEqual "Expected print-definition to be False by default"
                False flag_value
        , testCase "given explicitly is True" $ do
            let flag_value = willPrintDefinition $ runParser commandLineParser
                    ["mock/path/to/def", "--print-definition"]
            assertEqual "Expected --print-definition to give True"
                True flag_value
        , testCase "with `no` prefix is False" $ do
            let flag_value = willPrintDefinition $ runParser commandLineParser
                    ["mock/path/to/def", "--no-print-definition"]
            assertEqual "Expected --no-print-definition to give False"
                False flag_value
        ]
    , testGroup "print-pattern"
        [ testCase "default is False" $ do
            let flag_value = willPrintPattern $ runParser commandLineParser
                    ["mock/path/to/def"]
            assertEqual "Expected print-pattern to be False by default"
                False flag_value
        , testCase "given explicitly is True" $ do
            let flag_value = willPrintPattern $ runParser commandLineParser
                    ["mock/path/to/def", "--print-pattern"]
            assertEqual "Expected --print-pattern to give True"
                True flag_value
        , testCase "with `no` prefix is False" $ do
            let flag_value = willPrintPattern $ runParser commandLineParser
                    ["mock/path/to/def", "--no-print-pattern"]
            assertEqual "Expected --no-print-pattern to give False"
                False flag_value
        ]
    ]

test_options :: [TestTree]
test_options =
    [ testGroup "pattern and module must go together"
        [ testCase "pattern only" $ do
            let result = runParser' commandLineParser
                    ["mock/path/to/def", "--pattern", "mock/path/to/pat"]
            assertBool "Expected passing only the pattern option to fail"
                $ isNothing result
        , testCase "module only" $ do
            let result = runParser' commandLineParser
                    ["mock/path/to/def", "--module", "mock_module"]
            assertBool "Expected passing only the module option to fail"
                $ isNothing result
        , testCase "pattern and module" $ do
            let result = runParser' commandLineParser
                    ["mock/path/to/def", "--pattern", "mock/path/to/pat"
                    , "--module", "mock_module"]
            assertBool "Expected passing both pattern and module options to not fail"
                $ isJust result
        ]
    ]

runParser' :: Parser a -> [String] -> Maybe a
runParser' parser input = getParseResult parserResult
  where
    parserInfo = info parser mempty
    parserResult = execParserPure defaultPrefs parserInfo input

runParser :: Parser a -> [String] -> a
runParser parser input = fromJust $ runParser' parser input
