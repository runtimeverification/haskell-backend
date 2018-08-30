module Test.Kore.AST.Common (test_withSort, test_id, test_prettyPrintAstLocation, test_astTraversals) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertBool, assertEqual, assertFailure, testCase )
import Test.Tasty.HUnit.Extensions

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.Implicit.ImplicitSorts
import Test.Kore(testId)

test_withSort :: TestTree
test_withSort =
    testGroup "withSort"
        [ testCase "withSort fills missing sort"
            (assertSortedStub
                SortedPattern
                    { sortedPatternPattern = TopPattern Top
                        { topSort = sortListMetaSort }
                    , sortedPatternSort = sortListMetaSort
                    }
                (withSort sortListMetaSort
                    (UnsortedPatternStub
                        (\sort -> TopPattern Top { topSort = sort })
                    )
                )
            )
        , testCase "withSort keeps the same sort sort"
            (assertSortedStub
                SortedPattern
                    { sortedPatternPattern = TopPattern Top
                        { topSort = sortListMetaSort }
                    , sortedPatternSort = sortListMetaSort
                    }
                (withSort sortListMetaSort
                    (SortedPatternStub SortedPattern
                        { sortedPatternPattern =
                            TopPattern Top { topSort = sortListMetaSort }
                        , sortedPatternSort = sortListMetaSort
                        }
                    )
                )
            )
        , testCase "withSort keeps the same sort sort"
            (assertError
                (assertSubstring
                    "Expecting unmatched sorts error"
                    (  "Unmatched sorts: "
                    ++ "SortActualSort (SortActual {sortActualName = Id "
                    ++ "{getId = \"#PatternList\", "
                    ++ "idLocation = AstLocationImplicit}, "
                    ++ "sortActualSorts = []}) "
                    ++ "and SortActualSort (SortActual {sortActualName = Id "
                    ++ "{getId = \"#SortList\""
                    ++ ", idLocation = AstLocationImplicit}"
                    ++ ", sortActualSorts = []})."
                    )
                )
                (withSort patternListMetaSort
                    (SortedPatternStub SortedPattern
                        { sortedPatternPattern =
                            TopPattern Top { topSort = sortListMetaSort }
                        , sortedPatternSort = sortListMetaSort
                        }
                    )
                )
            )
        ]
  where
    assertSortedStub
        :: SortedPattern Meta Variable CommonKorePattern
        -> PatternStub Meta Variable CommonKorePattern
        -> IO ()
    assertSortedStub expectedSorted stub =
        case stub of
            UnsortedPatternStub _ ->
                assertFailure "Expected a sorted pattern stub"
            SortedPatternStub sorted ->
                assertEqual "Expecting a pattern with the given sort"
                    expectedSorted
                    sorted

test_prettyPrintAstLocation :: TestTree
test_prettyPrintAstLocation =
    testGroup "prettyPrintAstLocation"
        [ testCase "prints AstLocationNone"
            (assertEqual ""
                "<unknown location>"
                (prettyPrintAstLocation AstLocationNone)
            )
        , testCase "prints AstLocationImplicit"
            (assertEqual ""
                "<implicitly defined entity>"
                (prettyPrintAstLocation AstLocationImplicit)
            )
        , testCase "prints AstLocationGeneratedVariable"
            (assertEqual ""
                "<variable generated internally>"
                (prettyPrintAstLocation AstLocationGeneratedVariable)
            )
        , testCase "prints AstLocationFile"
            (assertEqual ""
                "some-file-name 10:3"
                (prettyPrintAstLocation
                    (AstLocationFile FileLocation
                        { fileName = "some-file-name"
                        , line = 10
                        , column = 3
                        }
                    )
                )
            )
        , testCase "prints AstLocationLifted"
            (assertEqual ""
                "<lifted(<implicitly defined entity>)>"
                (prettyPrintAstLocation (AstLocationLifted AstLocationImplicit))
            )
        ]

test_id :: TestTree
test_id =
    testGroup "Id"
        [ testCase "Id comparison"
            (do
                assertBool ""
                    (Id "a" AstLocationNone <= Id "b" AstLocationNone)
                assertBool ""
                    (Id "b" AstLocationNone >= Id "a" AstLocationNone)
                assertBool ""
                    (Id "a" AstLocationNone == Id "a" AstLocationNone)
            )
        , testCase "Id comparison ignores location"
            (do
                assertBool ""
                    (Id "a" AstLocationNone == Id "a" AstLocationImplicit)
                assertBool ""
                    (Id "a" AstLocationImplicit == Id "a" AstLocationNone)
            )
        , testCase "Id show"
            (assertEqual ""
                "Id {getId = \"a\", idLocation = AstLocationNone}"
                (show (Id "a" AstLocationNone))
            )
        , testCase "noLocationId"
            (assertEqual ""
                Id
                    { getId = "a"
                    , idLocation = AstLocationNone
                    }
                (noLocationId "a")
            )
        ]

test_astTraversals :: [TestTree]
test_astTraversals =
    [ testCase "Testing patternBottomUpVisitor"
        (assertEqual ""
            samplePatternExpected
            (patternBottomUpVisitor leftImplies samplePattern)
        )
    ]
  where
    leftImplies (ImpliesPattern ip) = impliesFirst ip
    leftImplies p = asKorePattern p
    samplePatternExpected :: CommonKorePattern
    samplePatternExpected =
        asKorePattern $ ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "sigma"
                , symbolOrAliasParams = []
                } :: SymbolOrAlias Object
            , applicationChildren =
                [ asKorePattern $ StringLiteralPattern $ StringLiteral "left1"
                ,  asKorePattern $ StringLiteralPattern $ StringLiteral "left2"
                ]
            }
    samplePattern =
        asKorePattern $ ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "sigma"
                , symbolOrAliasParams = []
                } :: SymbolOrAlias Object
            , applicationChildren =
                [ asKorePattern $ ImpliesPattern Implies
                    { impliesSort = SortVariableSort $ SortVariable $
                        testId "#a" :: Sort Meta
                    , impliesFirst = asKorePattern $ StringLiteralPattern
                        (StringLiteral "left1")
                    , impliesSecond = asKorePattern $ StringLiteralPattern
                        (StringLiteral "right1")
                    }
                ,  asKorePattern $ ImpliesPattern Implies
                    { impliesSort = SortVariableSort $ SortVariable $
                        testId "#b" :: Sort Meta
                    , impliesFirst = asKorePattern $ StringLiteralPattern
                        (StringLiteral "left2")
                    , impliesSecond = asKorePattern $ StringLiteralPattern
                        (StringLiteral "right2")
                    }
                ]
            }
