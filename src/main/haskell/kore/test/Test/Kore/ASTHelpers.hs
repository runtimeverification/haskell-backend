module Test.Kore.ASTHelpers (test_symbolOrAliasSorts) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Kore.AST.Common
import Kore.AST.Sentence
import Kore.ASTHelpers
import Kore.Error

import Test.Kore

test_symbolOrAliasSorts :: [TestTree]
test_symbolOrAliasSorts =
    [ testCase "simple result sort"
        (assertEqual "Expecting success"
            (applicationSorts [] simpleSortActual)
            (symbolOrAliasSorts
                []
                (symbolSentence [] [] simpleSortActual)
            )
        )
    , testCase "parameterized result sort"
        (assertEqual "Expecting success"
            (applicationSorts [] simpleSortActual)
            (symbolOrAliasSorts
                [simpleSortActual]
                (symbolSentence [sortVariable'] [] sortVariableSort')
            )
        )
    , testCase "complex parameterized result sort"
        (assertEqual "Expecting success"
            (applicationSorts [] complexSortActualSort)
            (symbolOrAliasSorts
                [simpleSortActual]
                (symbolSentence [sortVariable'] [] complexSortActualParam)
            )
        )
    , testCase "simple argument sort"
        (assertEqual "Expecting success"
            (applicationSorts [simpleSortActual] simpleSortActual)
            (symbolOrAliasSorts
                []
                (symbolSentence [] [simpleSortActual] simpleSortActual)
            )
        )
    , testCase "parameterized argument sort"
        (assertEqual "Expecting success"
            (applicationSorts [simpleSortActual] simpleSortActual)
            (symbolOrAliasSorts
                [simpleSortActual]
                (symbolSentence
                    [sortVariable'] [sortVariableSort'] simpleSortActual)
            )
        )
    , testCase "complex argument sort"
        (assertEqual "Expecting success"
            (applicationSorts [complexSortActualSort] simpleSortActual)
            (symbolOrAliasSorts
                [simpleSortActual]
                (symbolSentence
                    [sortVariable'] [complexSortActualParam] simpleSortActual)
            )
        )
    , testCase "sort variable not found"
        (assertEqual "Expecting error"
            (koreFail "Sort variable not found: 'sv'.")
            (symbolOrAliasSorts
                [simpleSortActual]
                (symbolSentence
                    [anotherSortVariable'] [sortVariableSort'] simpleSortActual)
            )
        )
    , testCase "more sorts than the declaration"
        (assertEqual "Expecting error"
            (koreFail "Application uses more sorts than the declaration.")
            (symbolOrAliasSorts
                [simpleSortActual, simpleSortActual]
                (symbolSentence
                    [sortVariable'] [simpleSortActual] simpleSortActual)
            )
        )
    , testCase "less sorts than the declaration"
        (assertEqual "Expecting error"
            (koreFail "Application uses less sorts than the declaration.")
            (symbolOrAliasSorts
                []
                (symbolSentence
                    [sortVariable'] [simpleSortActual] simpleSortActual)
            )
        )
    ]
  where
    simpleSortActual = sortActual "sa" []
    sortVariable' = sortVariable "sv"
    anotherSortVariable' = sortVariable "asv"
    sortVariableSort' = sortVariableSort "sv"
    complexSortActualParam = sortActual "sa" [sortVariableSort']
    complexSortActualSort = sortActual "sa" [simpleSortActual]

sortVariable :: String -> SortVariable level
sortVariable name =
    SortVariable { getSortVariable = testId name }

sortVariableSort :: String -> Sort level
sortVariableSort name =
    SortVariableSort (sortVariable name)

sortActual :: String -> [Sort level] -> Sort level
sortActual name sorts =
    SortActualSort SortActual
        { sortActualName = testId name
        , sortActualSorts = sorts
        }

applicationSorts
    :: [Sort level] -> Sort level -> Either b (ApplicationSorts level)
applicationSorts operandSorts resultSort =
    Right ApplicationSorts
        { applicationSortsOperands = operandSorts
        , applicationSortsResult = resultSort
        }

symbolSentence
    :: [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> KoreSentenceSymbol level
symbolSentence sortParameters operandSorts resultSort =
    SentenceSymbol
        { sentenceSymbolSymbol     = Symbol
            { symbolConstructor = testId "symb"
            , symbolParams = sortParameters
            }
        , sentenceSymbolSorts      = operandSorts
        , sentenceSymbolResultSort = resultSort
        , sentenceSymbolAttributes = Attributes []
        }
