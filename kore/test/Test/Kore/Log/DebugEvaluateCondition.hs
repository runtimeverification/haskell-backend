module Test.Kore.Log.DebugEvaluateCondition
    ( test_instance_Table_DebugEvaluateCondition
    ) where

import Prelude.Kore ()

import Test.Tasty

import Kore.Internal.Predicate
import Kore.Internal.TermLike
import Kore.Log.DebugEvaluateCondition

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_DebugEvaluateCondition :: TestTree
test_instance_Table_DebugEvaluateCondition =
    testTable @DebugEvaluateCondition
        [ DebugEvaluateCondition predicate1
        , DebugEvaluateCondition predicate2
        ]

predicate1, predicate2 :: Predicate Variable
predicate1 = makeEqualsPredicate_ (Mock.f Mock.a) (Mock.g Mock.b)
predicate2 = makeEqualsPredicate_ (Mock.g Mock.a) (Mock.h Mock.c)
