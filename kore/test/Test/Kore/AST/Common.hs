module Test.Kore.AST.Common (
    test_id,
    test_prettyPrintAstLocation,
) where

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
                    (locatedId "a" AstLocationNone <= locatedId "b" AstLocationNone)
                assertBool
                    ""
                    (locatedId "b" AstLocationNone >= locatedId "a" AstLocationNone)
                assertBool
                    ""
                    (locatedId "a" AstLocationNone == locatedId "a" AstLocationNone)
            )
        , testCase
            "Id comparison ignores location"
            ( do
                assertBool
                    ""
                    (locatedId "a" AstLocationNone == locatedId "a" AstLocationImplicit)
                assertBool
                    ""
                    (locatedId "a" AstLocationImplicit == locatedId "a" AstLocationNone)
            )
        , testCase
            "Id show"
            ( assertEqual
                ""
                "Id {getId = \"a\", idLocation = AstLocationNone}"
                (show (locatedId "a" AstLocationNone))
            )
        , testCase
            "noLocationId"
            ( assertEqual
                ""
                (locatedId "a" AstLocationNone)
                (noLocationId "a")
            )
        ]
