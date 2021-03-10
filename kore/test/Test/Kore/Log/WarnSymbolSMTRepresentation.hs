module Test.Kore.Log.WarnSymbolSMTRepresentation (
    test_instance_Table_WarnSymbolSMTRepresentation,
) where

import Prelude.Kore ()

import Test.Tasty

import Kore.Log.WarnSymbolSMTRepresentation

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_WarnSymbolSMTRepresentation :: TestTree
test_instance_Table_WarnSymbolSMTRepresentation =
    testTable @WarnSymbolSMTRepresentation [warn1, warn2]

warn1, warn2 :: WarnSymbolSMTRepresentation
warn1 = WarnSymbolSMTRepresentation Mock.aSymbol
warn2 = WarnSymbolSMTRepresentation Mock.bSymbol
