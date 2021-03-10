module Test.Kore.Log.ErrorBottomTotalFunction (
    test_instance_Table_ErrorBottomTotalFunction,
) where

import Prelude.Kore ()

import Test.Tasty

import Kore.Log.ErrorBottomTotalFunction

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_ErrorBottomTotalFunction :: TestTree
test_instance_Table_ErrorBottomTotalFunction =
    testTable @ErrorBottomTotalFunction [warn1, warn2]

warn1, warn2 :: ErrorBottomTotalFunction
warn1 = ErrorBottomTotalFunction Mock.a
warn2 = ErrorBottomTotalFunction Mock.b
