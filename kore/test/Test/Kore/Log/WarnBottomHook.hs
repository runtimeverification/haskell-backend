module Test.Kore.Log.WarnBottomHook
    ( test_instance_Table_WarnBottomHook
    ) where

import Test.Tasty

import Kore.Log.WarnBottomHook

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_WarnBottomHook :: TestTree
test_instance_Table_WarnBottomHook =
    testTable @WarnBottomHook
        [ WarnBottomHook { hook = "HOOK.a", term = Mock.a }
        , WarnBottomHook { hook = "HOOK.b", term = Mock.b }
        , WarnBottomHook { hook = "HOOK.c", term = Mock.c }
        ]
