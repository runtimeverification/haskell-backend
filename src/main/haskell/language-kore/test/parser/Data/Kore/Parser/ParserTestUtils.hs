module Data.Kore.Parser.ParserTestUtils where

import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Data.Either                      (isLeft)

data ParserTest a
    = Success { successInput :: String, successExpected :: a }
    | Failure { failureInput :: String, failureExpected :: String }
    | Skip [String]
    | FailureWithoutMessage [String]

parseTree :: (Show a, Eq a) => Parser.Parser a -> [ParserTest a] -> [TestTree]
parseTree parser = map (parseTest parser)

parseTest :: (Show a, Eq a) => Parser.Parser a -> ParserTest a -> TestTree
parseTest parser (Success successInput successExpected) =
    testCase
        ("Parsing '" ++ successInput ++ "'")
        (parseSuccess successExpected parser successInput)
parseTest parser (Failure failureInput failureExpected) =
    testCase
        ("Failing to parse '" ++ failureInput ++ "'")
        (parseFailureWithMessage failureExpected parser failureInput)
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
parseSkipTest _ (Success successInput _) =
    testCase
        ("Parsing success test '" ++ successInput ++ "'")
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
