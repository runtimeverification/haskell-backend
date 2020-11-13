module Test.Kore.Parser
    ( FailureTest (..)
    , ParserTest (..)
    , parseTree
    , parseSkipTree
    , success
    , SuccessfulTest (..)
    , parsesTo_
    , fails
    , parse'
    ) where

import Prelude.Kore

import Test.Tasty
    ( TestTree
    , testGroup
    )
import Test.Tasty.HUnit
    ( Assertion
    , assertBool
    , assertEqual
    , testCase
    )

import qualified Data.Bifunctor as Bifunctor
import Text.Megaparsec
    ( Parsec
    , ShowErrorComponent
    , eof
    , errorBundlePretty
    , parse
    )

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

parsesTo_ :: String -> a -> ParserTest a
parsesTo_ = success

fails :: String -> () -> ParserTest a
fails input _ = FailureWithoutMessage [input]

parseTree
    :: HasCallStack
    => (Show a, Eq a)
    => ShowErrorComponent e
    => Parsec e String a
    -> [ParserTest a]
    -> [TestTree]
parseTree parser = map (parseTest parser)

parseTest
    :: HasCallStack
    => (Show a, Eq a)
    => ShowErrorComponent e
    => Parsec e String a
    -> ParserTest a
    -> TestTree
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

parseSkipTree
    :: HasCallStack
    => Parser () -> [ParserTest ()] -> [TestTree]
parseSkipTree parser = map (parseSkipTest parser)

parseSkipTest
    :: HasCallStack
    => Parser ()
    -> ParserTest ()
    -> TestTree
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

parse' :: ShowErrorComponent e => Parsec e String a -> String -> Either String a
parse' parser input =
    parse (parser <* eof) "<test-string>" input
    & Bifunctor.first errorBundlePretty

parseSuccess
    :: HasCallStack
    => (Show a, Eq a)
    => ShowErrorComponent e
    => a -> Parsec e String a -> String -> Assertion
parseSuccess expected parser input =
    assertEqual "" (Right expected) (parse' parser input)

parseSkip :: ShowErrorComponent e => Parsec e String () -> String -> Assertion
parseSkip parser input =
    assertEqual "" (Right ()) (parse' parser input)

parseFailureWithoutMessage
    :: ShowErrorComponent e => Parsec e String a -> String -> Assertion
parseFailureWithoutMessage parser input =
    assertBool "" (isLeft (parse' parser input))

parseFailureWithMessage
    :: HasCallStack
    => (Show a, Eq a)
    => ShowErrorComponent e
    => String -> Parsec e String a -> String -> Assertion
parseFailureWithMessage expected parser input =
    assertEqual "" (Left expected) (parse' parser input)
