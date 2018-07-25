module Test.Kore.Parser.CString (test_cString) where

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
    , success (Input "\\U000120FF") (Expected "\73983")
    , success (Input "\\\\") (Expected "\\")
    , success (Input "\\'") (Expected "'")
    , success (Input "\\\"") (Expected "\"")
    , success (Input "\\?") (Expected "?")
    , success (Input "\\a") (Expected "\7")
    , success (Input "\\b") (Expected "\8")
    , success (Input "\\f") (Expected "\12")
    , success (Input "\\n") (Expected "\10")
    , success (Input "\\r") (Expected "\13")
    , success (Input "\\t") (Expected "\9")
    , success (Input "\\v") (Expected "\11")
    , success (Input "\\1") (Expected "\1")
    , success (Input "\\10") (Expected "\8")
    , success (Input "\\100") (Expected "\64")
    , success (Input "\\1000") (Expected ("\64" ++ "0"))
    , success (Input "\\xf") (Expected "\15")
    , success (Input "\\xfz") (Expected ("\15" ++ "z"))
    , success (Input "\\xff") (Expected "\255")
    , success (Input "\\xffz") (Expected ("\255" ++ "z"))
    , success (Input "\\u1ABC") (Expected "\6844")
    , success (Input "\\u1ABCD") (Expected ("\6844" ++ "D"))
    , success (Input "\\U000120FF") (Expected "\73983")
    , success (Input "\\U000120FFF") (Expected ("\73983" ++ "F"))
    , testProperty "QuickCheck Escape&Unescape" escapeUnescapeProp

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
        (Expected "unescapeCString : Unknown escape sequence '\\z'.")
    ]

newtype Input = Input String
newtype Expected = Expected String

success :: Input -> Expected -> TestTree
success (Input input) (Expected expected) =
    testCase
        ("Unescaping '" ++ input ++ "'.")
        (assertEqual "Expecting unescaping success."
            (Right expected)
            (unescapeCString input)
        )

failureWithMessage :: Input -> Expected -> TestTree
failureWithMessage (Input input) (Expected expected) =
    testCase
        ("Failing to unescape '" ++ input ++ "'.")
        (assertEqual "Expecting unescaping failure."
            (Left expected)
            (unescapeCString input)
        )

escapeUnescapeProp :: String -> Bool
escapeUnescapeProp str =
    Right str == unescapeCString (escapeCString str)
