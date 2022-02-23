module Test.Kore.Log.ErrorBottomTotalFunction (
    test_instance_Table_ErrorBottomTotalFunction,
) where

import Kore.Log.ErrorBottomTotalFunction
import Prelude.Kore ()
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.SQL
import Test.Tasty

test_instance_Table_ErrorBottomTotalFunction :: TestTree
test_instance_Table_ErrorBottomTotalFunction =
    testTable @ErrorBottomTotalFunction [warn1, warn2]

warn1, warn2 :: ErrorBottomTotalFunction
warn1 = ErrorBottomTotalFunction Mock.a
warn2 = ErrorBottomTotalFunction Mock.b
