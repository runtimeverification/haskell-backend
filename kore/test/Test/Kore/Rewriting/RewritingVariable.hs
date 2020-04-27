module Test.Kore.Rewriting.RewritingVariable
    ( test_FreshPartialOrd_RewritingVariable
    , test_FreshPartialOrd_UnifiedVariable_RewritingVariable
    , test_SortedVariable_RewritingVariable
    ) where

import Prelude.Kore

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import qualified Control.Lens as Lens

import Kore.Rewriting.RewritingVariable
import Kore.Syntax.Variable
import Kore.Variables.UnifiedVariable
import Pair

import Test.Kore
    ( testId
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Variables.Fresh
    ( relatedUnifiedVariableGen
    , relatedVariableGen
    , testFreshPartialOrd
    )
import Test.Tasty.HUnit.Ext

test_SortedVariable_RewritingVariable :: [TestTree]
test_SortedVariable_RewritingVariable =
    [ testCase "over lensVariableSort id === id -- RuleVariable" $ do
        let input = mkRuleVariable variable
        assertEqual "" input (Lens.over lensVariableSort id input)
    , testCase "over lensVariableSort id === id -- ConfigVariable" $ do
        let input = mkConfigVariable variable
        assertEqual "" input (Lens.over lensVariableSort id input)
    ]
  where
    variable = Variable (testId "x") mempty Mock.testSort

test_FreshPartialOrd_RewritingVariable :: TestTree
test_FreshPartialOrd_RewritingVariable =
    testGroup "instance FreshPartialOrd RewritingVariable"
    $ testFreshPartialOrd relatedRewritingVariableGen

test_FreshPartialOrd_UnifiedVariable_RewritingVariable :: TestTree
test_FreshPartialOrd_UnifiedVariable_RewritingVariable =
    testGroup "instance FreshPartialOrd (UnifiedVariable RewritingVariable)"
    $ testFreshPartialOrd relatedUnifiedRewritingVariableGen

relatedRewritingVariableGen :: Gen (Pair RewritingVariable)
relatedRewritingVariableGen =
    Gen.choice
    [ (fmap . fmap) mkRuleVariable relatedVariableGen
    , (fmap . fmap) mkConfigVariable relatedVariableGen
    ]

relatedUnifiedRewritingVariableGen
    :: Gen (Pair (UnifiedVariable RewritingVariable))
relatedUnifiedRewritingVariableGen =
    Gen.choice
    [ (fmap . fmap) mkUnifiedRuleVariable relatedUnifiedVariableGen
    , (fmap . fmap) mkUnifiedConfigVariable relatedUnifiedVariableGen
    ]
