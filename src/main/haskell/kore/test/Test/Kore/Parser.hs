module Test.Kore.Parser where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( Assertion, assertBool, assertEqual, testCase )

import Data.Either
       ( isLeft )

import Kore.Parser.ParserUtils

data SuccessfulTest a = SuccessfulTest
    { successInput    :: String
    , successExpected :: a
    }

data FailureTest = FailureTest
    { failureInput    :: String
    , failureExpected :: String
    }

data ParserTest a
    = Success (SuccessfulTest a)
    | Failure FailureTest
    | Skip [String]
    | FailureWithoutMessage [String]

success :: String -> a -> ParserTest a
success input expected = Success SuccessfulTest
    { successInput = input
    , successExpected = expected
    }

failure :: String -> String -> ParserTest a
failure input expected = Failure FailureTest
    { failureInput = input
    , failureExpected = expected
    }

parseTree :: (Show a, Eq a) => Parser a -> [ParserTest a] -> [TestTree]
parseTree parser = map (parseTest parser)

parseTest :: (Show a, Eq a) => Parser a -> ParserTest a -> TestTree
parseTest parser (Success test) =
    testCase
        ("Parsing '" ++ successInput test ++ "'")
        (parseSuccess (successExpected test) parser (successInput test))
parseTest parser (Failure test) =
    testCase
        ("Failing to parse '" ++ failureInput test ++ "'")
        (parseFailureWithMessage
            (failureExpected test) parser (failureInput test))
parseTest parser (FailureWithoutMessage tests) =
    testGroup "Tests Failing Without Message"
    (map
        (\input ->
            testCase
                ("Failing to parse '" ++ input ++ "'")
                (parseFailureWithoutMessage parser input)
        )
        tests
    )
parseTest _ (Skip tests) =
    testCase
        ("Parsing skip tests '" ++ show tests ++ "'")
        (assertBool "Not Expecting Skip Tests here" False)

parseSkipTree :: Parser () -> [ParserTest ()] -> [TestTree]
parseSkipTree parser = map (parseSkipTest parser)
parseSkipTest :: Parser () -> ParserTest () -> TestTree
parseSkipTest parser (Skip tests) =
    testGroup "Tests for Parsers not creating ASTs"
    (map
        (\input ->
            testCase
                ("Skipping '" ++ input ++ "'")
                (parseSkip parser input)
        )
        tests
    )
parseSkipTest _ (Success test) =
    testCase
        ("Parsing success test '" ++ successInput test ++ "'")
        (assertBool "Not Expecting Success Tests here" False)
parseSkipTest parser test = parseTest parser test

parseSuccess :: (Show a, Eq a) => a -> Parser a -> String -> Assertion
parseSuccess expected parser input =
    assertEqual
        "Expecting parse success!"
        (Right expected)
        (parseOnly (parser <* endOfInput) "<test-string>" input)

parseSkip :: Parser () -> String -> Assertion
parseSkip parser input =
    assertEqual
        "Expecting skip success!"
        (Right ())
        (parseOnly (parser <* endOfInput) "<test-string>" input)

parseFailureWithoutMessage :: Parser a -> String -> Assertion
parseFailureWithoutMessage parser input =
    assertBool
        "Expecting parse failure!"
        (isLeft
            (parseOnly (parser <* endOfInput) "<test-string>" input)
        )

parseFailureWithMessage
    :: (Show a, Eq a)
    => String -> Parser a -> String -> Assertion
parseFailureWithMessage expected parser input =
    assertEqual
        "Expecting parse failure!"
        (Left expected)
        (parseOnly (parser <* endOfInput) "<test-string>" input)
