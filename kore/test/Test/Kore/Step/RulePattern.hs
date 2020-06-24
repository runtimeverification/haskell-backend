module Test.Kore.Step.RulePattern
    ( test_freeVariables
    , test_refreshRule
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit.Ext

import Data.Default
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Step.RulePattern
import Kore.Step.Step
    ( refreshRule
    )

import qualified Test.Kore.Step.MockSymbols as Mock

test_freeVariables :: TestTree
test_freeVariables =
    testCase "Extract free variables" $ do
        let expect =
                foldMap (freeVariable . mkSomeVariable)
                [Mock.x, Mock.z, Mock.t, Mock.u]
            actual = freeVariables testRulePattern
        assertEqual "Expected free variables" expect actual

test_refreshRule :: [TestTree]
test_refreshRule =
    [ testCase "Rename target variables" $ do
        let avoiding :: FreeVariables VariableName
            avoiding = freeVariables testRulePattern
            (renaming, rulePattern') =
                refreshRule avoiding testRulePattern
            renamed = Set.fromList (Foldable.toList renaming)
            free' :: FreeVariables VariableName
            free' = freeVariables rulePattern'
            notAvoided (variableName -> x) =
                not (FreeVariables.isFreeVariable x avoiding)
        assertEqual
            "Expected to rename all free variables of original RulePattern"
            (FreeVariables.toNames avoiding)
            (Map.keysSet renaming)
        assertBool
            "Expected to renamed variables distinct from original variables"
            (all notAvoided renamed)
        assertBool
            "Expected no free variables in common with original RulePattern"
            (all notAvoided (FreeVariables.toList free'))
    , testCase "no stale variables" $ do
        let (renaming, _) = refreshRule mempty testRulePattern
        assertBool "expected not to rename variables" (null renaming)
    , testCase "stale existentials" $ do
        let input = testRulePattern { left = mkElemVar Mock.y }
            (_, RulePattern { rhs }) = refreshRule mempty input
        assertBool "expected to refresh existentials"
            (notElem Mock.y $ existentials rhs)
        assertBool "expected to substitute fresh variables"
            ((/=) (mkElemVar Mock.y) $ right rhs)
    ]

testRulePattern :: RulePattern VariableName
testRulePattern =
    RulePattern
        { left =
            -- Include an implicitly-quantified variable.
            mkElemVar Mock.x
        , antiLeft = Just $ mkElemVar Mock.u
        , requires = Predicate.makeCeilPredicate_ (mkElemVar Mock.z)
        , rhs = RHS
            { existentials = [Mock.y]
            , right = mkElemVar Mock.y
            , ensures = Predicate.makeCeilPredicate_ (mkElemVar Mock.t)
            }
        , attributes = def
        }
