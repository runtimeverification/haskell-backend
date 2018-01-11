module ParserTestUtils where

import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Data.Either                      (isLeft)

data Success a = Success { successInput :: String, successExpected :: a }
newtype Skip = Skip [String]
newtype Failure = Failure [String]

parseTree
    :: (Show a, Eq a) => Parser.Parser a -> [Success a] -> Failure -> [TestTree]
parseTree parser successTests failureTests =
    parseSuccessTree parser successTests
    ++
    parseFailureTree parser failureTests

skipTree :: Parser.Parser () -> Skip -> Failure -> [TestTree]
skipTree parser skipTests failureTests =
    parseSkipTree parser skipTests
    ++
    parseFailureTree parser failureTests

parseSuccessTree
    :: (Show a, Eq a) => Parser.Parser a -> [Success a] -> [TestTree]
parseSuccessTree parser =
    map
        (\test ->
            testCase
                ("Parsing '" ++ successInput test ++ "'")
                (parseSuccess (successExpected test) parser (successInput test))
        )

parseSkipTree :: Parser.Parser () -> Skip -> [TestTree]
parseSkipTree parser (Skip tests) =
    map
        (\input ->
            testCase
                ("Skipping '" ++ input ++ "'")
                (parseSkip parser input)
        )
        tests

parseFailureTree
    :: (Show a, Eq a) => Parser.Parser a -> Failure -> [TestTree]
parseFailureTree parser (Failure tests) =
    map
        (\input ->
            testCase
                ("Failing to parse '" ++ input ++ "'")
                (parseFailure parser input)
        )
        tests

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

parseFailure :: (Show a, Eq a) => Parser.Parser a -> String -> Assertion
parseFailure parser input =
    assertBool
        "Expecting parse failure!"
        (isLeft
            (Parser.parseOnly
                (parser <* Parser.endOfInput)
                (Char8.pack input)))
