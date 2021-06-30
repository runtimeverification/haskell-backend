module Test.Kore.Rewrite.RewritingVariable (
    test_FreshPartialOrd_RewritingVariableName,
    test_FreshPartialOrd_SomeVariableName_RewritingVariableName,
) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Kore.Rewrite.RewritingVariable
import Kore.Syntax.Variable
import Pair
import Prelude.Kore
import Test.Kore.Variables.Fresh (
    relatedVariableNameGen,
    someVariableNameGen,
    testFreshPartialOrd,
 )
import Test.Tasty

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
