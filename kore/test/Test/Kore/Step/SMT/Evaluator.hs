module Test.Kore.Step.SMT.Evaluator
    ( test_evaluableSyntaxPredicate
    , test_evaluableConditional
    , test_evaluableMultiOr
    , test_andNegation
    , test_Int_contradictions
    , test_Bool_contradictions
    ) where

import Prelude.Kore


import Hedgehog hiding
    ( property
    )
import Test.Tasty

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( make
    )
import Kore.Internal.Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeEqualsPredicate_
    , makeFalsePredicate_
    , makeNotPredicate
    , makeTruePredicate_
    )
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Data as Kore
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import Kore.Syntax.Variable
    ( Variable
    )
import SMT
    ( SMT
    )

import Test.Kore
import qualified Test.Kore.Builtin.Bool as Builtin.Bool
import Test.Kore.Builtin.Builtin
    ( testEnv
    )
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Builtin.Int
import Test.Kore.Internal.Predicate ()
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import qualified Test.Kore.Step.Simplification as Test
import Test.SMT
import Test.Tasty.HUnit.Ext

contradictoryPredicate :: Predicate Variable
contradictoryPredicate =
    makeAndPredicate
        (makeEqualsPredicate_
            (mkElemVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool False)
        )
        (makeEqualsPredicate_
            (mkElemVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool True)
        )

test_evaluableSyntaxPredicate :: [TestTree]
test_evaluableSyntaxPredicate =
    [ testCase "refutes false predicate" $ do
        let expected = Just False
        actual <- evaluatePredicate makeFalsePredicate_
        assertEqual "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Just False
        actual <- evaluatePredicate contradictoryPredicate
        assertEqual "x<0 and x>=0 refuted to false"
            expected actual
    ]

test_evaluableConditional :: [TestTree]
test_evaluableConditional =
    [ testCase "refutes false predicate" $ do
        let expected = Just False
        actual <- evaluateConditional Conditional
            { term = Mock.a
            , predicate = makeFalsePredicate_
            , substitution = mempty
            }
        assertEqual "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Just False
        actual <- evaluateConditional Conditional
            { term = Mock.a
            , predicate = contradictoryPredicate
            , substitution = mempty
            }
        assertEqual "x<0 and x>=0 refuted to false"
            expected actual
    ]

test_evaluableMultiOr :: [TestTree]
test_evaluableMultiOr =
    [ testCase "refutes false predicate" $ do
        let expected = MultiOr.make
                [ Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
                ]
        actual <- evaluateMultiOr
            (MultiOr.make
                [ Conditional
                    { term = Mock.a
                    , predicate = makeFalsePredicate_
                    , substitution = mempty
                    }
                , Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
                ]
            )
        assertEqual "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = MultiOr.make
                [ Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
                ]
        actual <- evaluateMultiOr
            (MultiOr.make
                [ Conditional
                    { term = Mock.a
                    , predicate = contradictoryPredicate
                    , substitution = mempty
                    }
                , Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
                ]
            )
        assertEqual "x<0 and x>=0 refuted to false"
            expected actual
    ]

evaluatePredicate
    :: Predicate Variable
    -> IO (Maybe Bool)
evaluatePredicate = evaluate

evaluateConditional
    :: Pattern Variable
    -> IO (Maybe Bool)
evaluateConditional = evaluate

evaluateMultiOr
    :: MultiOr (Conditional Variable (TermLike Variable))
    -> IO (MultiOr (Conditional Variable (TermLike Variable)))
evaluateMultiOr =
    runSimplifier Mock.env . SMT.Evaluator.filterMultiOr

evaluate
    :: SMT.Evaluator.Evaluable thing
    => thing
    -> IO (Maybe Bool)
evaluate = runSimplifier Mock.env . SMT.Evaluator.evaluate

test_andNegation :: TestTree
test_andNegation =
    testPropertyWithSolver
        "\\and{_}(φ, \\not{_}(φ)) === \\bottom"
        property
  where
    property = do
        let boolVariableGen = mkElemVar <$> elementVariableGen Builtin.boolSort
            boolPredicateGen =
                predicateChildGen boolVariableGen Builtin.boolSort
        predicate <- forAll (standaloneGen boolPredicateGen)
        actual <-
            evaluateSMT
                (makeAndPredicate
                    predicate
                    (makeNotPredicate predicate)
                )
        expected === actual
    expected = Just False

evaluateSMT
    :: Predicate Variable
    -> PropertyT SMT (Maybe Bool)
evaluateSMT = lift . Kore.runSimplifier testEnv . SMT.Evaluator.evaluate

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Id -> TermLike Variable
vInt s = mkElemVar (elemVarS s Builtin.intSort)

a, b, c :: TermLike Variable
a = vInt (testId "a")
b = vInt (testId "b")
c = vInt (testId "c")

vBool :: Id -> TermLike Variable
vBool s = mkElemVar (elemVarS s Builtin.boolSort)

p, q :: TermLike Variable
p = vBool (testId "p")
q = vBool (testId "q")

assertRefuted :: HasCallStack => Predicate Variable -> Assertion
assertRefuted prop = do
    let expect = Just False
    actual <- Test.runSimplifier testEnv $ SMT.Evaluator.decidePredicate prop
    assertEqual "" expect actual

true, false :: TermLike Variable
true = Builtin.Bool.asInternal True
false = Builtin.Bool.asInternal False

int :: Integer -> TermLike Variable
int = Builtin.Int.intLiteral

test_Int_contradictions :: [TestTree]
test_Int_contradictions =
    [ testCase "a < 0 ∧ 0 < a" . assertRefuted
        $ makeEqualsPredicate_ true
        $ andBool (a `ltInt` int 0) (int 0 `ltInt` a)
    , testCase "(a + a < a + b) ∧ (b + b < a + b)" . assertRefuted
        $ makeEqualsPredicate_ true
        $ andBool
            ((a `addInt` a) `ltInt` (a `addInt` b))
            ((b `addInt` b) `ltInt` (a `addInt` b))
    , testCase "¬(a < b → b < c → a < c)" . assertRefuted
        $ makeEqualsPredicate_ false
        $ impliesBool (a `ltInt` b) (impliesBool (b `ltInt` c) (a `ltInt` c))
    , testCase "1 + 2 a (odd) = 2 b (even)" . assertRefuted
        $ makeEqualsPredicate_ true
        $ eqInt
            (addInt (int 1) (int 2 `mulInt` a))
            (int 2 `mulInt` b)
    , testCase "¬((0 - a² = b²) → a = 0)" . assertRefuted
        $ makeEqualsPredicate_ false
        $ impliesBool
            (eqInt (int 0 `subInt` (a `mulInt` a)) (b `mulInt` b))
            (eqInt a (int 0))
    , testCase "f(0) = 123 ∧ f(0) = 456  -- uninterpreted functions"
        . assertRefuted
        $ makeEqualsPredicate_ true
        $ andBool
            (eqInt (dummyInt (int 0)) (int 123))
            (eqInt (dummyInt (int 0)) (int 456))
    , testCase "¬(0 < a → (a / 2) < a)" . assertRefuted
        $ makeEqualsPredicate_ false
        $ impliesBool (int 0 `ltInt` a) (ltInt (a `tdivInt` int 2) a)
    , testCase "¬(2 a % 2 = 0)" . assertRefuted
        $ makeEqualsPredicate_ false
        $ eqInt (tmodInt (a `mulInt` int 2) (int 2)) (int 0)
    ]

test_Bool_contradictions :: [TestTree]
test_Bool_contradictions =
    [ testCase "¬(((p → q) → p) → p)  -- Pierce" . assertRefuted
        $ makeEqualsPredicate_ false
        $ ((p `impliesBool` q) `impliesBool` p) `impliesBool` p
    , testCase "¬(¬(p ∨ q) = ¬p ∧ ¬q)  -- de Morgan" . assertRefuted
        $ makeEqualsPredicate_ false
        $ eqBool (notBool (p `orBool` q)) (andBool (notBool p) (notBool q))
    , testCase "¬⊤" . assertRefuted $ makeNotPredicate makeTruePredicate_
    , testCase "¬(¬p = p → false)" . assertRefuted
        $ makeNotPredicate
        $ makeEqualsPredicate_ true
        $ eqBool (notBool p) (p `impliesBool` false)
    ]
