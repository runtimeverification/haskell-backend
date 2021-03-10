module Test.Kore.Rewriting.RewritingVariable (
    test_FreshPartialOrd_RewritingVariableName,
    test_FreshPartialOrd_SomeVariableName_RewritingVariableName,
) where

import Prelude.Kore

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Kore.Rewriting.RewritingVariable
import Kore.Syntax.Variable
import Pair

import Test.Kore.Variables.Fresh (
    relatedVariableNameGen,
    someVariableNameGen,
    testFreshPartialOrd,
 )

test_FreshPartialOrd_RewritingVariableName :: TestTree
test_FreshPartialOrd_RewritingVariableName =
    testGroup "instance FreshPartialOrd RewritingVariableName" $
        testFreshPartialOrd relatedRewritingVariableNameGen

test_FreshPartialOrd_SomeVariableName_RewritingVariableName :: TestTree
test_FreshPartialOrd_SomeVariableName_RewritingVariableName =
    testGroup "instance FreshPartialOrd (SomeVariableName RewritingVariableName)" $
        testFreshPartialOrd relatedSomeRewritingVariableGen

relatedRewritingVariableNameGen :: Gen (Pair RewritingVariableName)
relatedRewritingVariableNameGen =
    Gen.choice
        [ (fmap . fmap) mkRuleVariable relatedVariableNameGen
        , (fmap . fmap) mkConfigVariable relatedVariableNameGen
        ]

relatedSomeRewritingVariableGen ::
    Gen (Pair (SomeVariableName RewritingVariableName))
relatedSomeRewritingVariableGen =
    someVariableNameGen relatedRewritingVariableNameGen
