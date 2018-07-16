module Test.Data.Kore.Step.Condition.Condition (test_condition) where

import           Test.Tasty                         (TestTree)
import           Test.Tasty.HUnit                   (testCase)

import           Test.Data.Kore.Comparators         ()

import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Sorts
import           Data.Kore.Step.Condition.Condition

import           Test.Tasty.HUnit.Extensions

test_condition :: [TestTree]
test_condition =
    [ let
        makeAnd sort c1 c2 = fst (makeEvaluatedAnd sort c1 c2)
      in
        testCase "And truth table"
            (do
                assertEqualWithExplanation "false and false = false"
                    ConditionFalse
                    (makeAnd sortSort ConditionFalse ConditionFalse)
                assertEqualWithExplanation "false and true = false"
                    ConditionFalse
                    (makeAnd sortSort ConditionFalse ConditionTrue)
                assertEqualWithExplanation "true and false = false"
                    ConditionFalse
                    (makeAnd sortSort ConditionTrue ConditionFalse)
                assertEqualWithExplanation "true and true = true"
                    ConditionTrue
                    (makeAnd sortSort ConditionTrue ConditionTrue)
            )
    , let
        makeOr sort c1 c2 = fst (makeEvaluatedOr sort c1 c2)
      in
        testCase "Or truth table"
            (do
                assertEqualWithExplanation "false or false = false"
                    ConditionFalse
                    (makeOr sortSort ConditionFalse ConditionFalse)
                assertEqualWithExplanation "false or true = true"
                    ConditionTrue
                    (makeOr sortSort ConditionFalse ConditionTrue)
                assertEqualWithExplanation "true or false = true"
                    ConditionTrue
                    (makeOr sortSort ConditionTrue ConditionFalse)
                assertEqualWithExplanation "true or true = true"
                    ConditionTrue
                    (makeOr sortSort ConditionTrue ConditionTrue)
            )
    , let
        makeImplies sort c1 c2 = fst (makeEvaluatedImplies sort c1 c2)
      in
        testCase "Implies truth table"
            (do
                assertEqualWithExplanation "false implies false = true"
                    ConditionTrue
                    (makeImplies sortSort ConditionFalse ConditionFalse)
                assertEqualWithExplanation "false implies true = true"
                    ConditionTrue
                    (makeImplies sortSort ConditionFalse ConditionTrue)
                assertEqualWithExplanation "true implies false = false"
                    ConditionFalse
                    (makeImplies sortSort ConditionTrue ConditionFalse)
                assertEqualWithExplanation "true implies true = true"
                    ConditionTrue
                    (makeImplies sortSort ConditionTrue ConditionTrue)
            )
    , let
        makeIff sort c1 c2 = fst (makeEvaluatedIff sort c1 c2)
      in
        testCase "Iff truth table"
            (do
                assertEqualWithExplanation "false iff false = true"
                    ConditionTrue
                    (makeIff sortSort ConditionFalse ConditionFalse)
                assertEqualWithExplanation "false iff true = false"
                    ConditionFalse
                    (makeIff sortSort ConditionFalse ConditionTrue)
                assertEqualWithExplanation "true iff false = false"
                    ConditionFalse
                    (makeIff sortSort ConditionTrue ConditionFalse)
                assertEqualWithExplanation "true iff true = true"
                    ConditionTrue
                    (makeIff sortSort ConditionTrue ConditionTrue)
            )
    , let
        makeNot sort c2 = fst (makeEvaluatedNot sort c2)
      in
        testCase "Not truth table"
            (do
                assertEqualWithExplanation "not false = true"
                    ConditionTrue
                    (makeNot sortSort ConditionFalse)
                assertEqualWithExplanation "not true = false"
                    ConditionFalse
                    (makeNot sortSort ConditionTrue)
            )
    ]

sortSort :: ConditionSort Meta
sortSort = ConditionSort (asAst SortSort)
