module Test.Kore.Log.WarnFunctionWithoutEvaluators (
    test_instance_Table_WarnFunctionWithoutEvaluators,
) where

import Prelude.Kore ()

import Test.Tasty

import Kore.Log.WarnFunctionWithoutEvaluators

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_WarnFunctionWithoutEvaluators :: TestTree
test_instance_Table_WarnFunctionWithoutEvaluators =
    testTable @WarnFunctionWithoutEvaluators [warn1, warn2]

warn1, warn2 :: WarnFunctionWithoutEvaluators
warn1 = WarnFunctionWithoutEvaluators Mock.aSymbol
warn2 = WarnFunctionWithoutEvaluators Mock.bSymbol
