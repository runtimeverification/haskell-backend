module Test.Kore.Parser.CString
    ( test_cString
    , test_idemUnescapeEscape
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )
import Test.Tasty.QuickCheck
       ( testProperty )

import Kore.Parser.CString

test_cString :: [TestTree]
test_cString =
    [ success (Input "hello") (Expected "hello")
    , success (Input "") (Expected "")
    , success (Input "\\\\") (Expected "\\")
    , success (Input "\\'") (Expected "'")
    , success (Input "\\\"") (Expected "\"")
    , success (Input "\\b") (Expected "\x08")
    , success (Input "\\t") (Expected "\x09")
    , success (Input "\\n") (Expected "\x0A")
    , success (Input "\\f") (Expected "\x0C")
    , success (Input "\\r") (Expected "\x0D")
    , success (Input "\\u1ABC") (Expected "\x1ABC")
    , success (Input "\\u1ABCD") (Expected ['\x1ABC', 'D'])
    , success (Input "\\U000120FF") (Expected "\x120FF")
    , success (Input "\\U000120FFF") (Expected ['\x120FF', 'F'])

    , failureWithMessage
        (Input "\\")
        (Expected unexpectedEndOfInput)

    , failureWithMessage
        (Input "\\UFFFFFFFF")
        (Expected
            "Character code 4294967295 outside of the representable codes.")
    , failureWithMessage
        (Input "\\u00F")
        (Expected "Invalid unicode sequence length.")
    {- TODO(virgil: Add  nice error message for this.
    , failureWithMessage
        (Input "\\u00Fz")
        (Expected "Invalid unicode sequence length.")
    -}
    , failureWithMessage
        (Input "\\U000000F")
        (Expected "Invalid unicode sequence length.")
    {- TODO(virgil: Add  nice error message for this.
    , failureWithMessage
        (Input "\\U000000Fz")
        (Expected "Invalid unicode sequence length.")
    -}
    , failureWithMessage
        (Input "\\z")
        (Expected (unknownEscapeSequence 'z'))
    , failureWithMessage
        (Input "\\?")
        (Expected (unknownEscapeSequence '?'))
    , failureWithMessage
        (Input "\\a")
        (Expected (unknownEscapeSequence 'a'))
    , failureWithMessage
        (Input "\\v")
        (Expected (unknownEscapeSequence 'v'))
    , failureWithMessage
        (Input "\\1")
        (Expected (unknownEscapeSequence '1'))
    , failureWithMessage
        (Input "\\10")
        (Expected (unknownEscapeSequence '1'))
    , failureWithMessage
        (Input "\\x08")
        (Expected (unknownEscapeSequence 'x'))
    ]

newtype Input = Input String
newtype Expected = Expected String

success :: Input -> Expected -> TestTree
success (Input input) (Expected expected) =
    testCase
        ("Unescaping '" ++ input ++ "'")
        (assertEqual ""
            (Right expected)
            (unescapeCString input)
        )

failureWithMessage :: Input -> Expected -> TestTree
failureWithMessage (Input input) (Expected expected) =
    testCase
        ("Failing to unescape '" ++ input ++ "'")
        (assertEqual ""
            (Left expected)
            (unescapeCString input)
        )

test_idemUnescapeEscape :: TestTree
test_idemUnescapeEscape =
    testProperty "Idempotency (unescape . escape)" escapeUnescapeProp
  where
    escapeUnescapeProp str =
        Right str == (unescapeCString . escapeCString) str
