module Test.Kore.Log.WarnFunctionWithoutEvaluators (
    test_instance_Table_WarnFunctionWithoutEvaluators,
) where

import Kore.Log.WarnFunctionWithoutEvaluators
import Prelude.Kore ()
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.SQL
import Test.Tasty

test_instance_Table_WarnFunctionWithoutEvaluators :: TestTree
test_instance_Table_WarnFunctionWithoutEvaluators =
    testTable @WarnFunctionWithoutEvaluators [warn1, warn2]

warn1, warn2 :: WarnFunctionWithoutEvaluators
warn1 = WarnFunctionWithoutEvaluators Mock.aSymbol
warn2 = WarnFunctionWithoutEvaluators Mock.bSymbol
