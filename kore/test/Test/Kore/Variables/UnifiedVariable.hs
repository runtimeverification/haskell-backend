module Test.Kore.Variables.UnifiedVariable
    ( test_isSetVar
    , test_isElemVar
    -- * Re-exports
    , module Kore.Syntax.Variable
    , module Kore.Variables.UnifiedVariable
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Syntax.Variable
import Kore.Variables.UnifiedVariable

import Test.Kore
    ( testId
    )
import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Ext

test_isSetVar :: [TestTree]
test_isSetVar =
    [ test "set variable"
        (True, mkSomeVariable $ mkSetVariable (testId "@x") testSort)
    , test "element variable"
        (False, mkSomeVariable $ mkElementVariable (testId "x") testSort)
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> (Bool, SomeVariable VariableName)
        -> TestTree
    test name (expect, input) =
        testCase name $ do
            let actual = isSetVar input
            assertEqual "" expect actual

test_isElemVar :: [TestTree]
test_isElemVar =
    [ test "set variable"
        (False, mkSomeVariable $ mkSetVariable (testId "@x") testSort)
    , test "element variable"
        (True, mkSomeVariable $ mkElementVariable (testId "x") testSort)
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> (Bool, SomeVariable VariableName)
        -> TestTree
    test name (expect, input) =
        testCase name $ do
            let actual = isElemVar input
            assertEqual "" expect actual
