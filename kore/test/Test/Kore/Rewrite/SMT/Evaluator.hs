{-# LANGUAGE TemplateHaskell #-}

module Test.Kore.Rewrite.SMT.Evaluator (
    test_evaluableSyntaxPredicate,
    test_evaluableConditional,
    test_evaluableMultiOr,
    test_andNegation,
    test_Int_contradictions,
    test_Bool_contradictions,
) where

import Hedgehog hiding (
    property,
 )
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.MultiOr qualified as MultiOr (
    make,
 )
import Kore.Internal.Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeEqualsPredicate,
    makeFalsePredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.TermLike
import Kore.Log.DecidePredicateUnknown (
    OnDecidePredicateUnknown (ErrorDecidePredicateUnknown),
    srcLoc,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
 )
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator
import Kore.Simplify.Simplify qualified as Kore
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.Bool qualified as Builtin.Bool
import Test.Kore.Builtin.Builtin (
    testEnv,
 )
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.Definition qualified as Builtin
import Test.Kore.Builtin.Int qualified as Builtin.Int
import Test.Kore.Internal.Predicate ()
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Kore.Simplify qualified as Test
import Test.SMT
import Test.Tasty
import Test.Tasty.HUnit.Ext

contradictoryPredicate :: Predicate VariableName
contradictoryPredicate =
    makeAndPredicate
        ( makeEqualsPredicate
            (mkElemVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool False)
        )
        ( makeEqualsPredicate
            (mkElemVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool True)
        )

test_evaluableSyntaxPredicate :: [TestTree]
test_evaluableSyntaxPredicate =
    [ testCase "refutes false predicate" $ do
        let expected = Just False
        actual <- evaluatePredicate makeFalsePredicate
        assertEqual "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Just False
        actual <- evaluatePredicate contradictoryPredicate
        assertEqual
            "x<0 and x>=0 refuted to false"
            expected
            actual
    ]

test_evaluableConditional :: [TestTree]
test_evaluableConditional =
    [ testCase "refutes false predicate" $ do
        let expected = Just False
        actual <-
            evaluateConditional
                Conditional
                    { term = Mock.a
                    , predicate = makeFalsePredicate
                    , substitution = mempty
                    }
        assertEqual "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Just False
        actual <-
            evaluateConditional
                Conditional
                    { term = Mock.a
                    , predicate = contradictoryPredicate
                    , substitution = mempty
                    }
        assertEqual
            "x<0 and x>=0 refuted to false"
            expected
            actual
    ]

test_evaluableMultiOr :: [TestTree]
test_evaluableMultiOr =
    [ testCase "refutes false predicate" $ do
        let expected =
                MultiOr.make
                    [ Conditional
                        { term = Mock.b
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluateMultiOr
                ( MultiOr.make
                    [ Conditional
                        { term = Mock.a
                        , predicate = makeFalsePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.b
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
        assertEqual "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected =
                MultiOr.make
                    [ Conditional
                        { term = Mock.b
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluateMultiOr
                ( MultiOr.make
                    [ Conditional
                        { term = Mock.a
                        , predicate = contradictoryPredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.b
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
        assertEqual
            "x<0 and x>=0 refuted to false"
            expected
            actual
    ]

evaluatePredicate ::
    Predicate VariableName ->
    IO (Maybe Bool)
evaluatePredicate =
    runSimplifierSMT Mock.env
        . flip (SMT.Evaluator.evalPredicate $ ErrorDecidePredicateUnknown $srcLoc Nothing) Nothing

evaluateConditional ::
    Pattern VariableName ->
    IO (Maybe Bool)
evaluateConditional =
    runSimplifierSMT Mock.env
        . flip (SMT.Evaluator.evalConditional $ ErrorDecidePredicateUnknown $srcLoc Nothing) Nothing

evaluateMultiOr ::
    MultiOr (Conditional VariableName (TermLike VariableName)) ->
    IO (MultiOr (Conditional VariableName (TermLike VariableName)))
evaluateMultiOr =
    runSimplifierSMT Mock.env . SMT.Evaluator.filterMultiOr $srcLoc

test_andNegation :: TestTree
test_andNegation =
    testPropertyWithSolver
        "\\and{_}(φ, \\not{_}(φ)) === \\bottom"
        property
  where
    property = do
        let boolVariableGen = mkElemVar <$> elementVariableGen Builtin.boolSort
            boolPredicateGen =
                predicateChildGen
                    boolVariableGen
                    (Just Builtin.boolSort)
                    Builtin.boolSort
        predicate <- forAll (standaloneGen boolPredicateGen)
        actual <-
            evaluateSMT
                ( makeAndPredicate
                    predicate
                    (makeNotPredicate predicate)
                )
        expected === actual
    expected = Just False

evaluateSMT ::
    Predicate VariableName ->
    PropertyT SMT (Maybe Bool)
evaluateSMT =
    lift
        . Kore.runSimplifier testEnv
        . flip (SMT.Evaluator.evalPredicate $ ErrorDecidePredicateUnknown $srcLoc Nothing) Nothing

-- ----------------------------------------------------------------
-- Refute Int predicates

vInt :: Id -> TermLike RewritingVariableName
vInt s = mkElemVar (configElementVariableFromId s Builtin.intSort)

a, b, c :: TermLike RewritingVariableName
a = vInt (testId "a")
b = vInt (testId "b")
c = vInt (testId "c")

vBool :: Id -> TermLike RewritingVariableName
vBool s = mkElemVar (configElementVariableFromId s Builtin.boolSort)

p, q :: TermLike RewritingVariableName
p = vBool (testId "p")
q = vBool (testId "q")

assertRefuted :: HasCallStack => Predicate RewritingVariableName -> Assertion
assertRefuted prop = do
    let expect = Just False
    actual <-
        SMT.Evaluator.decidePredicate
            (ErrorDecidePredicateUnknown $srcLoc Nothing)
            SideCondition.top
            []
            prop
            & Test.runSimplifierSMT testEnv
    assertEqual "" expect actual

true, false :: TermLike RewritingVariableName
true = Builtin.Bool.asInternal True
false = Builtin.Bool.asInternal False

int :: Integer -> TermLike RewritingVariableName
int = Builtin.Int.intLiteral

test_Int_contradictions :: [TestTree]
test_Int_contradictions =
    [ testCase "a < 0 ∧ 0 < a" . assertRefuted $
        makeEqualsPredicate true $
            andBool (a `ltInt` int 0) (int 0 `ltInt` a)
    , testCase "(a + a < a + b) ∧ (b + b < a + b)" . assertRefuted $
        makeEqualsPredicate true $
            andBool
                ((a `addInt` a) `ltInt` (a `addInt` b))
                ((b `addInt` b) `ltInt` (a `addInt` b))
    , testCase "¬(a < b → b < c → a < c)" . assertRefuted $
        makeEqualsPredicate false $
            impliesBool (a `ltInt` b) (impliesBool (b `ltInt` c) (a `ltInt` c))
    , testCase "1 + 2 a (odd) = 2 b (even)" . assertRefuted $
        makeEqualsPredicate true $
            eqInt
                (addInt (int 1) (int 2 `mulInt` a))
                (int 2 `mulInt` b)
    , testCase "¬((0 - a² = b²) → a = 0)" . assertRefuted $
        makeEqualsPredicate false $
            impliesBool
                (eqInt (int 0 `subInt` (a `mulInt` a)) (b `mulInt` b))
                (eqInt a (int 0))
    , testCase "f(0) = 123 ∧ f(0) = 456  -- uninterpreted functions"
        . assertRefuted
        $ makeEqualsPredicate true
        $ andBool
            (eqInt (dummyFunctionalInt (int 0)) (int 123))
            (eqInt (dummyFunctionalInt (int 0)) (int 456))
    , testCase "¬(0 < a → (a / 2) < a)" . assertRefuted $
        makeEqualsPredicate false $
            impliesBool (int 0 `ltInt` a) (ltInt (a `tdivInt` int 2) a)
    , testCase "¬(2 a % 2 = 0)" . assertRefuted $
        makeEqualsPredicate false $
            eqInt (tmodInt (a `mulInt` int 2) (int 2)) (int 0)
    ]

test_Bool_contradictions :: [TestTree]
test_Bool_contradictions =
    [ testCase "¬(((p → q) → p) → p)  -- Pierce" . assertRefuted $
        makeEqualsPredicate false $
            ((p `impliesBool` q) `impliesBool` p) `impliesBool` p
    , testCase "¬(¬(p ∨ q) = ¬p ∧ ¬q)  -- de Morgan" . assertRefuted $
        makeEqualsPredicate false $
            eqBool (notBool (p `orBool` q)) (andBool (notBool p) (notBool q))
    , testCase "¬⊤" . assertRefuted $ makeNotPredicate makeTruePredicate
    , testCase "¬(¬p = p → false)" . assertRefuted $
        makeNotPredicate $
            makeEqualsPredicate true $
                eqBool (notBool p) (p `impliesBool` false)
    ]
