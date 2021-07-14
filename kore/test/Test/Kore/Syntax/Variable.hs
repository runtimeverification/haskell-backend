module Test.Kore.Syntax.Variable (
    test_isSetVariable,
    test_isElementVariable,
    hprop_instance_Injection_SomeVariableName_ElementVariableName,
    hprop_instance_Injection_SomeVariableName_SetVariableName,

    -- * Re-exports
    module Kore.Syntax.Variable,
) where

import Kore.Syntax.Variable
import Prelude.Kore
import Test.Injection
import Test.Kore (
    testId,
 )
import Test.Kore.Rewrite.MockSymbols (
    testSort,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_isSetVariable :: [TestTree]
test_isSetVariable =
    [ test
        "set variable"
        (True, mkSomeVariable $ mkSetVariable (testId "@x") testSort)
    , test
        "element variable"
        (False, mkSomeVariable $ mkElementVariable (testId "x") testSort)
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        (Bool, SomeVariable VariableName) ->
        TestTree
    test name (expect, input) =
        testCase name $ do
            let actual = isSetVariable input
            assertEqual "" expect actual

test_isElementVariable :: [TestTree]
test_isElementVariable =
    [ test
        "set variable"
        (False, mkSomeVariable $ mkSetVariable (testId "@x") testSort)
    , test
        "element variable"
        (True, mkSomeVariable $ mkElementVariable (testId "x") testSort)
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        (Bool, SomeVariable VariableName) ->
        TestTree
    test name (expect, input) =
        testCase name $ do
            let actual = isElementVariable input
            assertEqual "" expect actual

hprop_instance_Injection_SomeVariableName_ElementVariableName :: Property
hprop_instance_Injection_SomeVariableName_ElementVariableName =
    hpropInjection @(SomeVariableName Int8) (ElementVariableName <$> genInt8)

hprop_instance_Injection_SomeVariableName_SetVariableName :: Property
hprop_instance_Injection_SomeVariableName_SetVariableName =
    hpropInjection @(SomeVariableName Int8) (SetVariableName <$> genInt8)
