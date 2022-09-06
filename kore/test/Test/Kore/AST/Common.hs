module Test.Kore.AST.Common (
    test_id,
    test_prettyPrintAstLocation,
) where

import Data.InternedText (internText)
import Kore.Syntax.Id
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit

test_prettyPrintAstLocation :: TestTree
test_prettyPrintAstLocation =
    testGroup
        "prettyPrintAstLocation"
        [ testCase
            "prints AstLocationNone"
            ( assertEqual
                ""
                "<unknown location>"
                (prettyPrintAstLocation AstLocationNone)
            )
        , testCase
            "prints AstLocationImplicit"
            ( assertEqual
                ""
                "<implicitly defined entity>"
                (prettyPrintAstLocation AstLocationImplicit)
            )
        , testCase
            "prints AstLocationGeneratedVariable"
            ( assertEqual
                ""
                "<variable generated internally>"
                (prettyPrintAstLocation AstLocationGeneratedVariable)
            )
        , testCase
            "prints AstLocationFile"
            ( assertEqual
                ""
                "some-file-name 10:3"
                ( prettyPrintAstLocation
                    ( AstLocationFile
                        FileLocation
                            { fileName = "some-file-name"
                            , line = 10
                            , column = 3
                            }
                    )
                )
            )
        ]

test_id :: TestTree
test_id =
    testGroup
        "Id"
        [ testCase
            "Id comparison"
            ( do
                assertBool
                    ""
                    (Id "a" AstLocationNone <= Id "b" AstLocationNone)
                assertBool
                    ""
                    (Id "b" AstLocationNone >= Id "a" AstLocationNone)
                assertBool
                    ""
                    (Id "a" AstLocationNone == Id "a" AstLocationNone)
            )
        , testCase
            "Id comparison ignores location"
            ( do
                assertBool
                    ""
                    (Id "a" AstLocationNone == Id "a" AstLocationImplicit)
                assertBool
                    ""
                    (Id "a" AstLocationImplicit == Id "a" AstLocationNone)
            )
        , testCase
            "Id show"
            ( assertEqual
                ""
                "InternedId {getInternedId = \"a\", internedIdLocation = AstLocationNone}"
                (show (Id "a" AstLocationNone))
            )
        , testCase
            "noLocationId"
            ( assertEqual
                ""
                InternedId
                    { getInternedId = internText "a"
                    , internedIdLocation = AstLocationNone
                    }
                (noLocationId "a")
            )
        ]
