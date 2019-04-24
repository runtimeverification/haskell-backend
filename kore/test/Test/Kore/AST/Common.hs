module Test.Kore.AST.Common
    ( test_withSort
    , test_id
    , test_prettyPrintAstLocation
    ) where

import Test.Tasty
import Test.Tasty.HUnit
       ( assertBool, assertEqual, assertFailure, testCase )

import           Kore.AST.Pure
import qualified Kore.Domain.Builtin as Domain

import           Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_withSort :: TestTree
test_withSort =
    testGroup "withSort"
        [ testCase "withSort fills missing sort"
            (assertSortedStub
                SortedPattern
                    { sortedPatternPattern = TopPattern Top
                        { topSort = Mock.testSort }
                    , sortedPatternSort = Mock.testSort
                    }
                (withSort Mock.testSort
                    (UnsortedPatternStub
                        (\sort -> TopPattern Top { topSort = sort })
                    )
                )
            )
        , testCase "withSort keeps the same sort sort"
            (assertSortedStub
                SortedPattern
                    { sortedPatternPattern = TopPattern Top
                        { topSort = Mock.testSort }
                    , sortedPatternSort = Mock.testSort
                    }
                (withSort Mock.testSort
                    (SortedPatternStub SortedPattern
                        { sortedPatternPattern =
                            TopPattern Top { topSort = Mock.testSort }
                        , sortedPatternSort = Mock.testSort
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
                    ++ "{getId = \"testSort0\", "
                    ++ "idLocation = AstLocationTest}, "
                    ++ "sortActualSorts = []}) "
                    ++ "and SortActualSort (SortActual {sortActualName = Id "
                    ++ "{getId = \"testSort1\""
                    ++ ", idLocation = AstLocationTest}"
                    ++ ", sortActualSorts = []})."
                    )
                )
                (withSort Mock.testSort0
                    (SortedPatternStub SortedPattern
                        { sortedPatternPattern =
                            TopPattern Top { topSort = Mock.testSort1 }
                        , sortedPatternSort = Mock.testSort1
                        }
                    )
                :: PatternStub Meta Domain.Builtin Variable ()
                )
            )
        ]
  where
    assertSortedStub
        :: SortedPattern Meta Domain.Builtin Variable ParsedPattern
        -> PatternStub Meta Domain.Builtin Variable ParsedPattern
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
