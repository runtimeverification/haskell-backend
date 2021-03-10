module Test.Kore.Step.ClaimPattern (
    test_freeVariables,
    test_refreshRule,
) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit.Ext

import Data.Default
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike hiding (
    substitute,
 )
import Kore.Rewriting.RewritingVariable
import Kore.Rewriting.UnifyingRule
import Kore.Step.ClaimPattern

import qualified Test.Kore.Step.MockSymbols as Mock

test_freeVariables :: TestTree
test_freeVariables =
    testCase "Extract free variables" $ do
        let expect =
                foldMap
                    (freeVariable . mkSomeVariable)
                    [x, z, t]
            actual = freeVariables testRulePattern
        assertEqual "Expected free variables" expect actual

test_refreshRule :: [TestTree]
test_refreshRule =
    [ testCase "Rename target variables" $ do
        let avoiding :: FreeVariables RewritingVariableName
            avoiding = freeVariables testRulePattern
            (renaming, rulePattern') =
                refreshRule avoiding testRulePattern
            renamed = Set.fromList (Prelude.Kore.toList renaming)
            free' :: FreeVariables RewritingVariableName
            free' = freeVariables rulePattern'
            notAvoided (variableName -> var) =
                not (FreeVariables.isFreeVariable var avoiding)
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
    , testGroup "stale existentials" $
        let assertions (renaming, claim@ClaimPattern{existentials}) = do
                assertBool
                    "expected to refresh existentials"
                    (notElem y existentials)
                assertBool
                    "expected to substitute fresh variables"
                    (notElem (inject y) $ FreeVariables.toList (freeVariablesRight claim))
                assertBool
                    "expected not to rename free variables"
                    (null renaming)
         in [ testCase "from outside" $ do
                let stale = freeVariable (inject y)
                assertions $ refreshRule stale testRulePattern
            , testCase "from left-hand side" $ do
                let input =
                        testRulePattern
                            { left =
                                Pattern.fromTermAndPredicate
                                    (mkElemVar y)
                                    ( Predicate.makeCeilPredicate
                                        (mkElemVar z)
                                    )
                            }
                assertions $ refreshRule mempty input
            ]
    ]

testRulePattern :: ClaimPattern
testRulePattern =
    ClaimPattern
        { left =
            -- Include an implicitly-quantified variable.
            Pattern.fromTermAndPredicate
                (mkElemVar x)
                (Predicate.makeCeilPredicate (mkElemVar z))
        , existentials = [y]
        , right =
            Pattern.fromTermAndPredicate
                (mkElemVar y)
                (Predicate.makeCeilPredicate (mkElemVar t))
                & OrPattern.fromPattern
        , attributes = def
        }

x, y, z, t :: ElementVariable RewritingVariableName
x = mapElementVariable (pure mkRuleVariable) Mock.x
y = mapElementVariable (pure mkRuleVariable) Mock.y
z = mapElementVariable (pure mkRuleVariable) Mock.z
t = mapElementVariable (pure mkRuleVariable) Mock.t
