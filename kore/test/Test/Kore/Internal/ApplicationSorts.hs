module Test.Kore.Internal.ApplicationSorts
    ( test_symbolOrAliasSorts
    ) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( assertEqual
    , testCase
    )

import Kore.Error
import Kore.Internal.ApplicationSorts
import Kore.Syntax
import Kore.Syntax.Definition

import Test.Kore

test_symbolOrAliasSorts :: [TestTree]
test_symbolOrAliasSorts =
    [ success "simple result sort"
        (applicationSorts [] simpleSortActual)
        (symbolOrAliasSorts [] (symbolSentence [] [] simpleSortActual))
    , success "parameterized result sort"
        (applicationSorts [] simpleSortActual)
        (symbolOrAliasSorts
            [simpleSortActual]
            (symbolSentence [sortVariable'] [] sortVariableSort')
        )
    , success "complex parameterized result sort"
        (applicationSorts [] complexSortActualSort)
        (symbolOrAliasSorts
            [simpleSortActual]
            (symbolSentence [sortVariable'] [] complexSortActualParam)
        )
    , success "simple argument sort"
        (applicationSorts [simpleSortActual] simpleSortActual)
        (symbolOrAliasSorts
            []
            (symbolSentence [] [simpleSortActual] simpleSortActual)
        )
    , success "parameterized argument sort"
        (applicationSorts [simpleSortActual] simpleSortActual)
        (symbolOrAliasSorts
            [simpleSortActual]
            (symbolSentence
                [sortVariable'] [sortVariableSort'] simpleSortActual)
        )
    , success "complex argument sort"
        (applicationSorts [complexSortActualSort] simpleSortActual)
        (symbolOrAliasSorts
            [simpleSortActual]
            (symbolSentence
                [sortVariable'] [complexSortActualParam] simpleSortActual)
        )
    , testCase "sort variable not found"
        (assertEqual "Expecting error"
            (koreFail "Sort variable not found: 'sv'."
                :: Either (Error e) ApplicationSorts)
            (symbolOrAliasSorts
                [simpleSortActual]
                (symbolSentence
                    [anotherSortVariable'] [sortVariableSort'] simpleSortActual)
            )
        )
    , testCase "more sorts than the declaration"
        (assertEqual "Expecting error"
            (koreFail "Application uses more sorts than the declaration."
                :: Either (Error e) ApplicationSorts)
            (symbolOrAliasSorts
                [simpleSortActual, simpleSortActual]
                (symbolSentence
                    [sortVariable'] [simpleSortActual] simpleSortActual)
            )
        )
    , testCase "less sorts than the declaration"
        (assertEqual "Expecting error"
            (koreFail "Application uses less sorts than the declaration."
                :: Either (Error e) ApplicationSorts)
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
    success name expect actual =
        testCase name $ assertEqual "Expecting success" (Right expect) actual

symbolSentence
    :: [SortVariable]
    -> [Sort]
    -> Sort
    -> ParsedSentenceSymbol
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
