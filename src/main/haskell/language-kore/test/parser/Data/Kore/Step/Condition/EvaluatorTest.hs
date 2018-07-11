{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Step.Condition.EvaluatorTest (conditionEvaluatorTests) where

import           Test.Tasty                           (TestTree, testGroup)
import           Test.Tasty.HUnit                     (testCase)

import           Data.Kore.AST.Common                 (Application (..),
                                                       AstLocation (..),
                                                       Id (..), Pattern (..),
                                                       Sort, SymbolOrAlias (..))
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureToKore             (patternKoreToPure)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Comparators                ()
import           Data.Kore.Error
import           Data.Kore.MetaML.AST                 (CommonMetaPattern)
import           Data.Kore.Step.Condition.Condition
import           Data.Kore.Step.Condition.Evaluator   (evaluateFunctionCondition)
import           Data.Kore.Step.Function.Data         (CommonPurePatternFunctionEvaluator (..),
                                                       FunctionResult (..),
                                                       FunctionResultProof (..))
import           Data.Kore.Step.Function.Mocks        (mockFunctionEvaluator)
import           Data.Kore.Variables.Fresh.IntCounter

import           Test.Tasty.HUnit.Extensions

conditionEvaluatorTests :: TestTree
conditionEvaluatorTests =
    testGroup
        "Condition evaluator tests"
        [ testCase "And truth table"
            (do
                assertEqualWithExplanation "false and false = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort sortSortFalse sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "false and true = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort sortSortFalse sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true and false = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort sortSortTrue sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "true and true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort sortSortTrue sortSortTrue)
                        )
                    )
            )
        , testCase "Or truth table"
            (do
                assertEqualWithExplanation "false or false = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort sortSortFalse sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "false or true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort sortSortFalse sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true or false = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort sortSortTrue sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "true or true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort sortSortTrue sortSortTrue)
                        )
                    )
            )
        , testCase "Implies truth table"
            (do
                assertEqualWithExplanation "false implies false = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort sortSortFalse sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "false implies true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort sortSortFalse sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true implies false = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort sortSortTrue sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "true implies true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort sortSortTrue sortSortTrue)
                        )
                    )
            )
        , testCase "Iff truth table"
            (do
                assertEqualWithExplanation "false iff false = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort sortSortFalse sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "false iff true = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort sortSortFalse sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true iff false = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort sortSortTrue sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "true iff true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort sortSortTrue sortSortTrue)
                        )
                    )
            )
        , testCase "Not truth table"
            (do
                assertEqualWithExplanation "not false = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaNot SortSort sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "not true = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaNot SortSort sortSortTrue)
                        )
                    )
            )
        , let
            falseChild = metaNot SortSort sortSortTrue
            trueChild = metaNot SortSort sortSortFalse
          in
            testCase "Evaluates children"
            (do
                assertEqualWithExplanation "true and <true-child> = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort sortSortTrue trueChild)
                        )
                    )
                assertEqualWithExplanation "<true-child> and true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort trueChild sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true and <false-child> = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaAnd SortSort sortSortTrue falseChild)
                        )
                    )
                assertEqualWithExplanation "false or <true-child> = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort sortSortFalse trueChild)
                        )
                    )
                assertEqualWithExplanation "<true-child> or false = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort trueChild sortSortFalse)
                        )
                    )
                assertEqualWithExplanation "false or <false-child> = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaOr SortSort sortSortFalse falseChild)
                        )
                    )
                assertEqualWithExplanation "true implies <true-child> = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort sortSortTrue trueChild)
                        )
                    )
                assertEqualWithExplanation "<true-child> implies true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort trueChild sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true implies <false-child> = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaImplies SortSort sortSortTrue falseChild)
                        )
                    )
                assertEqualWithExplanation "true iff <true-child> = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort sortSortTrue trueChild)
                        )
                    )
                assertEqualWithExplanation "<true-child> iff true = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort trueChild sortSortTrue)
                        )
                    )
                assertEqualWithExplanation "true iff <false-child> = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaIff SortSort sortSortTrue falseChild)
                        )
                    )
                assertEqualWithExplanation "not <true-child> = false"
                    ConditionFalse
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaNot SortSort trueChild)
                        )
                    )
                assertEqualWithExplanation "not <false-child> = true"
                    ConditionTrue
                    (evaluateCondition
                        (mockFunctionEvaluator [])
                        (ConditionSort sortSort)
                        (unevaluatedCondition
                            (metaNot SortSort falseChild)
                        )
                    )
            )
        , let
            fOfX = metaF (x PatternSort)
            gOfX = metaG (x PatternSort)
            hOfX = metaH (x PatternSort)
          in
            testCase "Evaluates equals"
                (do
                    assertEqualWithExplanation "f(x) /= g(x)"
                        ConditionFalse
                        (evaluateCondition
                            (mockFunctionEvaluator [])
                            (ConditionSort sortSort)
                            (unevaluatedCondition
                                (metaEquals (ResultSort SortSort) PatternSort
                                    fOfX
                                    gOfX
                                )
                            )
                        )
                    assertEqualWithExplanation
                        "f(x) = g(x) if f(x) => h(x) and g(x) => h(x)"
                        ConditionTrue
                        (evaluateCondition
                            (mockFunctionEvaluator
                                [   ( asPureMetaPattern fOfX
                                    ,   ( FunctionResult
                                            { functionResultPattern =
                                                asPureMetaPattern hOfX
                                            , functionResultCondition =
                                                ConditionTrue
                                            }
                                        , FunctionResultProof
                                        )
                                    )
                                ,   ( asPureMetaPattern gOfX
                                    ,   ( FunctionResult
                                            { functionResultPattern =
                                                asPureMetaPattern hOfX
                                            , functionResultCondition =
                                                ConditionTrue
                                            }
                                        , FunctionResultProof
                                        )
                                    )
                                ]
                            )
                            (ConditionSort sortSort)
                            (unevaluatedCondition
                                (metaEquals (ResultSort SortSort) PatternSort
                                    (metaF (x PatternSort))
                                    (metaG (x PatternSort))
                                )
                            )
                        )
                    assertEqualWithExplanation
                        ("f(x) /= g(x) if f(x) => h(x) and g(x) => h(x) "
                            ++ "but incompatible f condition")
                        ConditionFalse
                        (evaluateCondition
                            (mockFunctionEvaluator
                                [   ( asPureMetaPattern fOfX
                                    ,   ( FunctionResult
                                            { functionResultPattern =
                                                asPureMetaPattern hOfX
                                            , functionResultCondition =
                                                ConditionFalse
                                            }
                                        , FunctionResultProof
                                        )
                                    )
                                ,   ( asPureMetaPattern gOfX
                                    ,   ( FunctionResult
                                            { functionResultPattern =
                                                asPureMetaPattern hOfX
                                            , functionResultCondition =
                                                ConditionTrue
                                            }
                                        , FunctionResultProof
                                        )
                                    )
                                ]
                            )
                            (ConditionSort sortSort)
                            (unevaluatedCondition
                                (metaEquals (ResultSort SortSort) PatternSort
                                    (metaF (x PatternSort))
                                    (metaG (x PatternSort))
                                )
                            )
                        )
                    assertEqualWithExplanation
                        ("f(x) /= g(x) if f(x) => h(x) and g(x) => h(x) "
                            ++ "but incompatible g condition")
                        ConditionFalse
                        (evaluateCondition
                            (mockFunctionEvaluator
                                [   ( asPureMetaPattern fOfX
                                    ,   ( FunctionResult
                                            { functionResultPattern =
                                                asPureMetaPattern hOfX
                                            , functionResultCondition =
                                                ConditionTrue
                                            }
                                        , FunctionResultProof
                                        )
                                    )
                                ,   ( asPureMetaPattern gOfX
                                    ,   ( FunctionResult
                                            { functionResultPattern =
                                                asPureMetaPattern hOfX
                                            , functionResultCondition =
                                                ConditionFalse
                                            }
                                        , FunctionResultProof
                                        )
                                    )
                                ]
                            )
                            (ConditionSort sortSort)
                            (unevaluatedCondition
                                (metaEquals (ResultSort SortSort) PatternSort
                                    (metaF (x PatternSort))
                                    (metaG (x PatternSort))
                                )
                            )
                        )
                )
        ]

x :: MetaSort sort => sort -> MetaVariable sort
x = metaVariable "#x" AstLocationTest

sortSort :: Sort Meta
sortSort = asAst SortSort

sortSortTrue :: PatternTop SortSort Meta
sortSortTrue = metaTop SortSort

sortSortFalse :: PatternBottom SortSort Meta
sortSortFalse = metaBottom SortSort


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#f" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaF p1 = MetaF p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaF p1)
  where
    asProperPattern (MetaF p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = fSymbol
            , applicationChildren = [asAst p1]
            }
metaF
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaF p1
metaF = MetaF


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#g" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaG p1 = MetaG p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaG p1)
  where
    asProperPattern (MetaG p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = gSymbol
            , applicationChildren = [asAst p1]
            }
metaG
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaG p1
metaG = MetaG


hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#h" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaH p1 = MetaH p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaH p1)
  where
    asProperPattern (MetaH p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = hSymbol
            , applicationChildren = [asAst p1]
            }
metaH
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaH p1
metaH = MetaH


unevaluatedCondition
    :: ProperPattern Meta sort patt => patt -> UnevaluatedCondition Meta
unevaluatedCondition patt =
    UnevaluatedCondition (asPureMetaPattern patt)

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
asPureMetaPattern patt =
    case patternKoreToPure Meta (asAst patt) of
        Left err  -> error (printError err)
        Right pat -> pat

evaluateCondition
    :: CommonPurePatternFunctionEvaluator level
    -> ConditionSort level
    -> UnevaluatedCondition level
    -> EvaluatedCondition level
evaluateCondition
    functionEvaluator
    conditionSort
    condition
  =
    fst $ fst $ runIntCounter
        (evaluateFunctionCondition functionEvaluator conditionSort condition)
        0
