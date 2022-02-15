module Test.Kore.Parser (
    FailureTest (..),
    ParserTest (..),
    parseTree,
    lexTree,
    success,
    successes,
    SuccessfulTest (..),
    parsesTo_,
    fails,
    parse',
) where

import Data.Text (
    Text,
    unpack,
 )
import qualified Data.Text.Encoding as Text
import Kore.Parser.Lexer
import Kore.Parser.LexerWrapper
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

successes :: [Text] -> a -> [ParserTest a]
successes inputs expected = map (\input -> success input expected) inputs

parsesTo_ :: Text -> a -> ParserTest a
parsesTo_ = success

fails :: Text -> () -> ParserTest a
fails input _ = FailureWithoutMessage [input]

parseTree ::
    HasCallStack =>
    (Show a, Eq a) =>
    (FilePath -> Text -> Either String a) ->
    [ParserTest a] ->
    [TestTree]
parseTree parser = map (parseTest $ Parser parser)

parseTest ::
    HasCallStack =>
    (Show a, Eq a) =>
    Parser a ->
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

lexTree ::
    HasCallStack =>
    [ParserTest [TokenClass]] ->
    [TestTree]
lexTree = parseTree scanTokenClasses

scanTokens :: FilePath -> Text -> Either String [Token]
scanTokens fp input = alexScanTokens fp $ Text.encodeUtf8 input

scanTokenClasses :: FilePath -> Text -> Either String [TokenClass]
scanTokenClasses fp input =
    let tokens = scanTokens fp input
     in case tokens of
            Right r -> Right $ map getTokenClass r
            Left l -> Left l

parse' :: Parser a -> Text -> Either String a
parse' (Parser f) input =
    f "<test-string>" input

parseSuccess ::
    HasCallStack =>
    (Show a, Eq a) =>
    a ->
    Parser a ->
    Text ->
    Assertion
parseSuccess expected parser input =
    assertEqual "" (Right expected) (parse' parser input)

parseFailureWithoutMessage ::
    Parser a -> Text -> Assertion
parseFailureWithoutMessage parser input =
    assertBool "" (isLeft (parse' parser input))

parseFailureWithMessage ::
    HasCallStack =>
    (Show a, Eq a) =>
    String ->
    Parser a ->
    Text ->
    Assertion
parseFailureWithMessage expected parser input =
    assertEqual "" (Left expected) (parse' parser input)
