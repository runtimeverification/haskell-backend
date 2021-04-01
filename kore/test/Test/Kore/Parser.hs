{-# LANGUAGE Strict #-}

module Test.Kore.Parser (
    FailureTest (..),
    ParserTest (..),
    parseTree,
    parseSkipTree,
    success,
    SuccessfulTest (..),
    parsesTo_,
    fails,
    parse',
) where

import qualified Data.Bifunctor as Bifunctor
import Data.Text (
    Text,
    unpack,
 )
import Kore.Parser.ParserUtils
import Prelude.Kore
import Test.Tasty (
    TestTree,
    testGroup,
 )
import Test.Tasty.HUnit (
    Assertion,
    assertBool,
    assertEqual,
    testCase,
 )
import Text.Megaparsec (
    Parsec,
    ShowErrorComponent,
    eof,
    errorBundlePretty,
    parse,
 )

data SuccessfulTest a = SuccessfulTest
    { successInput :: Text
    , successExpected :: a
    }

data FailureTest = FailureTest
    { failureInput :: Text
    , failureExpected :: String
    }

data ParserTest a
    = Success (SuccessfulTest a)
    | Failure FailureTest
    | Skip [Text]
    | FailureWithoutMessage [Text]

success :: Text -> a -> ParserTest a
success input expected =
    Success
        SuccessfulTest
            { successInput = input
            , successExpected = expected
            }

parsesTo_ :: Text -> a -> ParserTest a
parsesTo_ = success

fails :: Text -> () -> ParserTest a
fails input _ = FailureWithoutMessage [input]

parseTree ::
    HasCallStack =>
    (Show a, Eq a) =>
    ShowErrorComponent e =>
    Parsec e Text a ->
    [ParserTest a] ->
    [TestTree]
parseTree parser = map (parseTest parser)

parseTest ::
    HasCallStack =>
    (Show a, Eq a) =>
    ShowErrorComponent e =>
    Parsec e Text a ->
    ParserTest a ->
    TestTree
parseTest parser (Success test) =
    testCase
        ("Parsing '" ++ unpack (successInput test) ++ "'")
        (parseSuccess (successExpected test) parser (successInput test))
parseTest parser (Failure test) =
    testCase
        ("Failing to parse '" ++ unpack (failureInput test) ++ "'")
        ( parseFailureWithMessage
            (failureExpected test)
            parser
            (failureInput test)
        )
parseTest parser (FailureWithoutMessage tests) =
    testGroup
        "Tests Failing Without Message"
        ( map
            ( \input ->
                testCase
                    ("Failing to parse '" ++ unpack input ++ "'")
                    (parseFailureWithoutMessage parser input)
            )
            tests
        )
parseTest _ (Skip tests) =
    testCase
        ("Parsing skip tests '" ++ show tests ++ "'")
        (assertBool "Not Expecting Skip Tests here" False)

parseSkipTree ::
    HasCallStack =>
    Parser () ->
    [ParserTest ()] ->
    [TestTree]
parseSkipTree parser = map (parseSkipTest parser)

parseSkipTest ::
    HasCallStack =>
    Parser () ->
    ParserTest () ->
    TestTree
parseSkipTest parser (Skip tests) =
    testGroup
        "Tests for Parsers not creating ASTs"
        ( map
            ( \input ->
                testCase
                    ("Skipping '" ++ unpack input ++ "'")
                    (parseSkip parser input)
            )
            tests
        )
parseSkipTest _ (Success test) =
    testCase
        ("Parsing success test '" ++ unpack (successInput test) ++ "'")
        (assertBool "Not Expecting Success Tests here" False)
parseSkipTest parser test = parseTest parser test

parse' :: ShowErrorComponent e => Parsec e Text a -> Text -> Either String a
parse' parser input =
    parse (parser <* eof) "<test-string>" input
        & Bifunctor.first errorBundlePretty

parseSuccess ::
    HasCallStack =>
    (Show a, Eq a) =>
    ShowErrorComponent e =>
    a ->
    Parsec e Text a ->
    Text ->
    Assertion
parseSuccess expected parser input =
    assertEqual "" (Right expected) (parse' parser input)

parseSkip :: ShowErrorComponent e => Parsec e Text () -> Text -> Assertion
parseSkip parser input =
    assertEqual "" (Right ()) (parse' parser input)

parseFailureWithoutMessage ::
    ShowErrorComponent e => Parsec e Text a -> Text -> Assertion
parseFailureWithoutMessage parser input =
    assertBool "" (isLeft (parse' parser input))

parseFailureWithMessage ::
    HasCallStack =>
    (Show a, Eq a) =>
    ShowErrorComponent e =>
    String ->
    Parsec e Text a ->
    Text ->
    Assertion
parseFailureWithMessage expected parser input =
    assertEqual "" (Left expected) (parse' parser input)
