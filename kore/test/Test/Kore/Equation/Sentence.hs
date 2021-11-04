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
import Kore.Internal.From
import qualified Kore.Validate as Validated
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Test.Tasty.HUnit.Ext

test_fromSentenceAxiom :: [TestTree]
test_fromSentenceAxiom =
    [ testCase "⌈I1 / I2⌉" $ do
        let term = Mock.tdivInt varI1 varI2
            -- TODO(Ana): this will need special handling
            -- when removing Ceil from TermLike
            original = mkCeil sortR term
            equation = mkEquation (mkCeil sortR term) (mkTop sortR)
        assertions (TermLike.fromTermLike original) equation
    , testCase "I1 < I2 = I2 >= I1" $ do
        let left = Mock.lessInt varI1 varI2
            right = Mock.greaterEqInt varI2 varI1
            original =
                Validated.mkEquals
                    sortR
                    (TermLike.fromTermLike left)
                    (TermLike.fromTermLike right)
            equation = mkEquation left right
        assertions original equation
    , testCase "⌈f(x))⌉ → f(x) = g(x) ∧ ⌈h(x)⌉" $ do
        let requires = fromCeil_ (Mock.f Mock.a)
            ensures = fromCeil_ (Mock.h Mock.b)
            left = Mock.f (mkElemVar Mock.x)
            right = Mock.g (mkElemVar Mock.x)
            original =
                Validated.mkImplies
                    (Predicate.fromPredicate sortR requires)
                    (Validated.mkEquals sortR
                        (TermLike.fromTermLike left)
                        (Validated.mkAnd
                            (TermLike.fromTermLike right)
                            (Predicate.fromPredicate Mock.testSort ensures)
                        )
                    )
            equation =
                (mkEquation left right)
                    { requires
                    , ensures
                    }
        assertions original equation
    , testCase "New equation form: ⌈f(x)⌉ ∧ ⌈y ∈ x⌉ → f(y) = g(x) ∧ ⌈h(x)⌉" $ do
        let requires = fromCeil_ (Mock.f Mock.a)
            ensures = fromCeil_ (Mock.h Mock.b)
            argument = fromIn_ (mkElemVar Mock.y) (mkElemVar Mock.x)
            argument' =
                fromAnd argument fromTop_
            left = Mock.f (mkElemVar Mock.y)
            right = Mock.g (mkElemVar Mock.y)
            original =
                Validated.mkImplies
                    (Validated.mkAnd
                        (Predicate.fromPredicate sortR requires)
                        (Predicate.fromPredicate sortR argument')
                    )
                    (Validated.mkEquals sortR
                        (TermLike.fromTermLike left)
                        (Validated.mkAnd
                            (TermLike.fromTermLike right)
                            (Predicate.fromPredicate Mock.testSort ensures)
                        )
                    )
            equation =
                (mkEquation left right)
                    { requires = requires
                    , argument = Just argument
                    , ensures = ensures
                    }
        assertions original equation
    ]
  where
    sortVariableR = SortVariable (testId "R")
    sortR = SortVariableSort sortVariableR
    assertions ::
        HasCallStack =>
        Validated.Pattern VariableName ->
        Equation VariableName ->
        Assertion
    assertions original equation = do
        actual <- expectRight $ test original
        assertEqual "Expected equation" equation actual
        assertEqual
            "Expected original pattern"
            original
            (toTermLike (Validated.patternSort original) actual)
    test original = fromSentenceAxiom (def, Validated.mkAxiom [sortVariableR] original)

varI1, varI2 :: TermLike VariableName
varI1 = mkElemVar $ mkElementVariable (testId "VarI1") Mock.intSort
varI2 = mkElemVar $ mkElementVariable (testId "VarI2") Mock.intSort
