module Test.Kore.Rewriting.RewritingVariable
    ( test_FreshPartialOrd_RewritingVariable
    , test_FreshPartialOrd_UnifiedVariable_RewritingVariable
    ) where

import Prelude.Kore

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Kore.Rewriting.RewritingVariable
import Kore.Variables.UnifiedVariable
import Pair

import Test.Kore.Variables.Fresh
    ( relatedUnifiedVariableGen
    , relatedVariableGen
    , testFreshPartialOrd
    )

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
