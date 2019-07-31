module Test.Kore.Step.Condition.Evaluator where

import Hedgehog hiding
       ( property )
import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Monad.Trans as Trans

import           Kore.Internal.Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeNotPredicate,
                 makeTruePredicate )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import           SMT
                 ( SMT )

import           Test.Kore
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import           Test.Kore.Builtin.Builtin
                 ( testEnv )
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Builtin.Int
import           Test.Kore.Predicate.Predicate ()
import           Test.SMT

test_andNegation :: TestTree
test_andNegation =
    testPropertyWithSolver
        "\\and{_}(φ, \\not{_}(φ)) === \\bottom"
        property
  where
    property = do
        let boolVariableGen = mkVar <$> variableGen Builtin.boolSort
            boolPredicateGen =
                predicateChildGen boolVariableGen Builtin.boolSort
        predicate <- forAll (standaloneGen boolPredicateGen)
        actual <-
            evaluate
                (makeAndPredicate
                    predicate
                    (makeNotPredicate predicate)
                )
        expected === actual
    expected = Just False

evaluate
    :: Syntax.Predicate Variable
    -> PropertyT SMT (Maybe Bool)
evaluate = Trans.lift . evalSimplifier testEnv . SMT.Evaluator.evaluate

noSimplification :: [(TermLike Variable, [Pattern Variable])]
noSimplification = []

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Id -> TermLike Variable
vInt s = mkVar (varS s Builtin.intSort)

a, b, c :: TermLike Variable
a = vInt (testId "a")
b = vInt (testId "b")
c = vInt (testId "c")

vBool :: Id -> TermLike Variable
vBool s = mkVar (varS s Builtin.boolSort)

p, q :: TermLike Variable
p = vBool (testId "p")
q = vBool (testId "q")

assertRefuted :: Syntax.Predicate Variable -> Assertion
assertRefuted prop = do
    let expect = Just False
    actual <-
        Test.SMT.runSMT $ evalSimplifier testEnv
        $ SMT.Evaluator.decidePredicate prop
    assertEqual "" expect actual

unit_1 :: Assertion
unit_1 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (andBool
            (a `ltInt` Builtin.Int.intLiteral 0)
            (Builtin.Int.intLiteral 0 `ltInt` a)
        )

unit_2 :: Assertion
unit_2 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (andBool
            ((a `addInt` a) `ltInt` (a `addInt` b))
            ((b `addInt` b) `ltInt` (a `addInt` b))
        )

unit_3 :: Assertion
unit_3 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (impliesBool
            (a `ltInt` b)
            (impliesBool (b `ltInt` c) (a `ltInt` c))
        )

unit_4 :: Assertion
unit_4 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (eqInt
            (addInt
                (Builtin.Int.intLiteral 1)
                (Builtin.Int.intLiteral 2 `mulInt` a)
            )
            (Builtin.Int.intLiteral 2 `mulInt` b)
        )

unit_5 :: Assertion
unit_5 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (impliesBool
            (eqInt
                (Builtin.Int.intLiteral 0 `subInt` (a `mulInt` a))
                (b `mulInt` b)
            )
            (eqInt a (Builtin.Int.intLiteral 0))
        )

-- | Tests that translateSMT can translate `f(0)` into a
-- dummy variable `<0>`, where `f` is an uninterpreted function.
unit_6 :: Assertion
unit_6 =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (andBool
            (eqInt
                (dummyInt (Builtin.Int.intLiteral 0))
                (Builtin.Int.intLiteral 123)
            )
            (eqInt
                (dummyInt (Builtin.Int.intLiteral 0))
                (Builtin.Int.intLiteral 456)
            )
        )

unit_div :: Assertion
unit_div =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (impliesBool
            (Builtin.Int.intLiteral 0 `ltInt` a)
            (ltInt (a `tdivInt` Builtin.Int.intLiteral 2) a)
        )

unit_mod :: Assertion
unit_mod =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (eqInt
            (tmodInt
                (a `mulInt` Builtin.Int.intLiteral 2)
                (Builtin.Int.intLiteral 2)
            )
            (Builtin.Int.intLiteral 0)
        )

unit_pierce :: Assertion
unit_pierce =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (((p `impliesBool` q) `impliesBool` p) `impliesBool` p)

unit_demorgan :: Assertion
unit_demorgan =
    assertRefuted
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal False)
        (eqBool
            (notBool (p `orBool` q))
            (andBool (notBool p) (notBool q))
        )

unit_true :: Assertion
unit_true =
    assertRefuted
    $ makeNotPredicate makeTruePredicate

unit_false :: Assertion
unit_false =
    assertRefuted
    $ makeNotPredicate
    $ makeEqualsPredicate
        (Builtin.Bool.asInternal True)
        (eqBool
            (notBool p)
            (p `impliesBool` Builtin.Bool.asInternal False)
        )
