module Data.Kore.AST.CommonTest (commonTests) where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertEqual, assertFailure,
                                                   testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Implicit.ImplicitSorts
import           Test.Tasty.HUnit.Extensions

commonTests :: TestTree
commonTests =
    testGroup "Common AST Tests"
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
                    ++ "{getId = \"#PatternList\"}, sortActualSorts = []}) "
                    ++ "and SortActualSort (SortActual {sortActualName = Id "
                    ++ "{getId = \"#SortList\"}, sortActualSorts = []})."
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

assertSortedStub
    :: SortedPattern Meta Variable UnifiedPattern
    -> PatternStub Meta Variable UnifiedPattern
    -> IO()
assertSortedStub expectedSorted stub =
    case stub of
        UnsortedPatternStub _ ->
            assertFailure "Expected a sorted pattern stub."
        SortedPatternStub sorted ->
            assertEqual "Expecting a pattern with the given sort"
                expectedSorted
                sorted
