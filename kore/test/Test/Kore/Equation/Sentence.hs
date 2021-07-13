module Test.Kore.Equation.Sentence (
    test_fromSentenceAxiom,
) where

import Data.Default (
    def,
 )
import Kore.Equation
import Kore.Internal.Predicate (
    wrapPredicate,
 )
import Kore.Internal.TermLike
import Prelude.Kore
import Test.Expect
import Test.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_fromSentenceAxiom :: [TestTree]
test_fromSentenceAxiom =
    [ testCase "⌈I1 / I2⌉" $ do
        let term = Mock.tdivInt varI1 varI2
            original = mkCeil sortR term
            equation = mkEquation (mkCeil sortR term) (mkTop sortR)
        assertions original equation
    , testCase "I1 < I2 = I2 >= I1" $ do
        let left = Mock.lessInt varI1 varI2
            right = Mock.greaterEqInt varI2 varI1
            original = mkEquals sortR left right
            equation = mkEquation left right
        assertions original equation
    , testCase "⌈f(x))⌉ → f(x) = g(x) ∧ ⌈h(x)⌉ (OLD FORMAT)" $ do
        -- This test case must be removed as part of https://github.com/kframework/kore/issues/2593
        let requires = mkCeil sortR (Mock.f Mock.a)
            ensures = mkCeil sortR (Mock.h Mock.b)
            left = Mock.f (mkElemVar Mock.x)
            right = Mock.g (mkElemVar Mock.x)
            original =
                mkImplies requires $
                    mkAnd (mkEquals sortR left right) ensures
            equation =
                (mkEquation left right)
                    { requires = wrapPredicate requires
                    , ensures = wrapPredicate ensures
                    }
        assertionsOld original equation
    , testCase "New equation form: ⌈f(x)⌉ ∧ ⌈y ∈ x⌉ → f(y) = g(x) ∧ ⌈h(x)⌉ (OLD FORMAT)" $ do
        -- This test case must be removed as part of https://github.com/kframework/kore/issues/2593
        let requires = mkCeil sortR (Mock.f Mock.a)
            ensures = mkCeil sortR (Mock.h Mock.b)
            argument = mkIn sortR (mkElemVar Mock.y) (mkElemVar Mock.x)
            argument' =
                mkAnd argument (mkTop sortR)
            left = Mock.f (mkElemVar Mock.y)
            right = Mock.g (mkElemVar Mock.y)
            original =
                mkImplies (mkAnd requires argument') $
                    mkAnd (mkEquals sortR left right) ensures
            equation =
                (mkEquation left right)
                    { requires = wrapPredicate requires
                    , argument = Just $ wrapPredicate argument
                    , ensures = wrapPredicate ensures
                    }
        assertionsOld original equation
    , testCase "⌈f(x))⌉ → f(x) = g(x) ∧ ⌈h(x)⌉" $ do
        let requires = mkCeil sortR (Mock.f Mock.a)
            ensures = mkCeil Mock.testSort (Mock.h Mock.b)
            left = Mock.f (mkElemVar Mock.x)
            right = Mock.g (mkElemVar Mock.x)
            original =
                mkImplies requires $
                    mkEquals sortR left (mkAnd right ensures)
            equation =
                (mkEquation left right)
                    { requires = wrapPredicate requires
                    , ensures = wrapPredicate ensures
                    }
        assertions original equation
    , testCase "New equation form: ⌈f(x)⌉ ∧ ⌈y ∈ x⌉ → f(y) = g(x) ∧ ⌈h(x)⌉" $ do
        let requires = mkCeil sortR (Mock.f Mock.a)
            ensures = mkCeil Mock.testSort (Mock.h Mock.b)
            argument = mkIn sortR (mkElemVar Mock.y) (mkElemVar Mock.x)
            argument' =
                mkAnd argument (mkTop sortR)
            left = Mock.f (mkElemVar Mock.y)
            right = Mock.g (mkElemVar Mock.y)
            original =
                mkImplies (mkAnd requires argument') $
                    mkEquals sortR left (mkAnd right ensures)
            equation =
                (mkEquation left right)
                    { requires = wrapPredicate requires
                    , argument = Just $ wrapPredicate argument
                    , ensures = wrapPredicate ensures
                    }
        assertions original equation
    ]
  where
    sortVariableR = SortVariable (testId "R")
    sortR = SortVariableSort sortVariableR
    assertions ::
        HasCallStack =>
        TermLike VariableName ->
        Equation VariableName ->
        Assertion
    assertions original equation = do
        actual <- expectRight $ test original
        assertEqual "Expected equation" equation actual
        assertEqual
            "Expected original pattern"
            original
            (toTermLike (termLikeSort original) actual)
    -- This function must be removed as part of https://github.com/kframework/kore/issues/2593
    assertionsOld ::
        HasCallStack =>
        TermLike VariableName ->
        Equation VariableName ->
        Assertion
    assertionsOld original equation = do
        actual <- expectRight $ test original
        assertEqual "Expected equation" equation actual
        assertEqual
            "Expected original pattern"
            original
            (toTermLikeOld (termLikeSort original) actual)
    test original = fromSentenceAxiom (def, mkAxiom [sortVariableR] original)

varI1, varI2 :: TermLike VariableName
varI1 = mkElemVar $ mkElementVariable (testId "VarI1") Mock.intSort
varI2 = mkElemVar $ mkElementVariable (testId "VarI2") Mock.intSort
