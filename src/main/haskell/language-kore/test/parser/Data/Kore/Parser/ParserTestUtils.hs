module Data.Kore.Parser.ParserTestUtils where

import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Data.Either                      (isLeft)

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

parseTree :: (Show a, Eq a) => Parser.Parser a -> [ParserTest a] -> [TestTree]
parseTree parser = map (parseTest parser)

parseTest :: (Show a, Eq a) => Parser.Parser a -> ParserTest a -> TestTree
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

parseSkipTree :: Parser.Parser () -> [ParserTest ()] -> [TestTree]
parseSkipTree parser = map (parseSkipTest parser)
parseSkipTest :: Parser.Parser () -> ParserTest () -> TestTree
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

parseSuccess :: (Show a, Eq a) => a -> Parser.Parser a -> String -> Assertion
parseSuccess expected parser input =
    assertEqual
        "Expecting parse success!"
        (Right expected)
        (Parser.parseOnly (parser <* Parser.endOfInput) (Char8.pack input))

parseSkip :: Parser.Parser () -> String -> Assertion
parseSkip parser input =
    assertEqual
        "Expecting skip success!"
        (Right ())
        (Parser.parseOnly (parser <* Parser.endOfInput) (Char8.pack input))

parseFailureWithoutMessage :: Parser.Parser a -> String -> Assertion
parseFailureWithoutMessage parser input =
    assertBool
        "Expecting parse failure!"
        (isLeft
            (Parser.parseOnly
                (parser <* Parser.endOfInput)
                (Char8.pack input)))

parseFailureWithMessage
    :: (Show a, Eq a)
    => String -> Parser.Parser a -> String -> Assertion
parseFailureWithMessage expected parser input =
    assertEqual
        "Expecting parse failure!"
        (Left expected)
        (Parser.parseOnly (parser <* Parser.endOfInput) (Char8.pack input))
