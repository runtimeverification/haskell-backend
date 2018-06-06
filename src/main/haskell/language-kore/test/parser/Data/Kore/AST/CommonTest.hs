module Data.Kore.AST.CommonTest (commonTests) where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertBool, assertEqual,
                                                   assertFailure, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Implicit.ImplicitSorts
import           Test.Tasty.HUnit.Extensions

commonTests :: TestTree
commonTests =
    testGroup "Common AST Tests"
        [ withSortTests
        , prettyPrintAstLocationTests
        , idTests
        ]

withSortTests :: TestTree
withSortTests =
    testGroup "withSort Tests"
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

prettyPrintAstLocationTests :: TestTree
prettyPrintAstLocationTests =
    testGroup "prettyPrintAstLocation Tests"
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

idTests :: TestTree
idTests =
    testGroup "Id Tests"
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

assertSortedStub
    :: SortedPattern Meta Variable CommonKorePattern
    -> PatternStub Meta Variable CommonKorePattern
    -> IO()
assertSortedStub expectedSorted stub =
    case stub of
        UnsortedPatternStub _ ->
            assertFailure "Expected a sorted pattern stub."
        SortedPatternStub sorted ->
            assertEqual "Expecting a pattern with the given sort"
                expectedSorted
                sorted
