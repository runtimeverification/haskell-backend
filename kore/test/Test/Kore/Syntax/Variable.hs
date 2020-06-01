module Test.Kore.Syntax.Variable
    ( test_isSetVariable
    , test_isElementVariable
    -- * Re-exports
    , module Kore.Syntax.Variable
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Syntax.Variable

import Test.Kore
    ( testId
    )
import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Ext

test_isSetVariable :: [TestTree]
test_isSetVariable =
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
            let actual = isSetVariable input
            assertEqual "" expect actual

test_isElementVariable :: [TestTree]
test_isElementVariable =
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
            let actual = isElementVariable input
            assertEqual "" expect actual
