module Test.Kore.Log.WarnBottomTotalFunction
    ( test_instance_Table_WarnBottomTotalFunction
    ) where

import Prelude.Kore ()

import Test.Tasty

import Kore.Log.WarnBottomTotalFunction

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_WarnBottomTotalFunction :: TestTree
test_instance_Table_WarnBottomTotalFunction =
    testTable @WarnBottomTotalFunction [warn1, warn2]

warn1, warn2 :: WarnBottomTotalFunction
warn1 = WarnBottomTotalFunction Mock.a
warn2 = WarnBottomTotalFunction Mock.b
