module Test.Kore.Rewrite.Implication (
    test_freeVariables,
    test_refreshRule,
    test_substitute,
) where

import Data.Default
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.Conditional (
    fromPredicate,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Rewrite.Implication
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.UnifyingRule
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

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
            renamed = Set.fromList (Foldable.toList renaming)
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
        let assertions (renaming, claim@Implication{existentials}) = do
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

test_substitute :: [TestTree]
test_substitute =
    [ testCase "does not capture free variables from the substitution" $ do
        let dummy =
                Pattern.fromCondition_
                    (fromPredicate Predicate.makeTruePredicate)
            right = OrPattern.fromTermLike (mkElemVar y)
            imp = mkImplication () dummy right [x]
            newImp =
                substitute
                    (Map.singleton (inject $ variableName y) (mkElemVar x))
                    imp
        assertBool "Expected the expected variable to not be captured" $
            not $ nullFreeVariables $ freeVariablesRight newImp
    ]

testRulePattern :: Implication ()
testRulePattern =
    Implication
        { left =
            -- Include an implicitly-quantified variable.
            Pattern.fromTermAndPredicate
                (mkElemVar x)
                (Predicate.makeCeilPredicate (mkElemVar z))
        , modality = ()
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
