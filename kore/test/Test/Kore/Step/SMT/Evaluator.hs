module Test.Kore.Step.SMT.Evaluator where

import Test.Tasty
import Test.Tasty.HUnit

import           Kore.Internal.Conditional
                 ( Conditional (Conditional) )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( make )
import           Kore.Internal.Pattern
                 ( Pattern )
import           Kore.Internal.TermLike
                 ( TermLike, mkVar )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import           Kore.Syntax.Variable
                 ( Variable )

import           Test.Kore.Comparators ()
import           Test.Kore.Predicate.Predicate ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.SMT
import           Test.Tasty.HUnit.Extensions

contradictoryPredicate :: Syntax.Predicate Variable
contradictoryPredicate =
    makeAndPredicate
        (makeEqualsPredicate
            (mkVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool False)
        )
        (makeEqualsPredicate
            (mkVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool True)
        )

test_evaluableSyntaxPredicate :: [TestTree]
test_evaluableSyntaxPredicate =
    [ testCase "refutes false predicate" $ do
        let expected = makeFalsePredicate
        actual <- evaluatePredicate makeFalsePredicate
        assertEqualWithExplanation "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = makeFalsePredicate
        actual <- evaluatePredicate contradictoryPredicate
        assertEqualWithExplanation "x<0 and x>=0 refuted to false"
            expected actual
    ]

test_evaluableConditional :: [TestTree]
test_evaluableConditional =
    [ testCase "refutes false predicate" $ do
        let expected = Conditional
                { term = Mock.a
                , predicate = makeFalsePredicate
                , substitution = mempty
                }
        actual <- evaluateConditional Conditional
            { term = Mock.a
            , predicate = makeFalsePredicate
            , substitution = mempty
            }
        assertEqualWithExplanation "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Conditional
                { term = Mock.a
                , predicate = makeFalsePredicate
                , substitution = mempty
                }
        actual <- evaluateConditional Conditional
            { term = Mock.a
            , predicate = contradictoryPredicate
            , substitution = mempty
            }
        assertEqualWithExplanation "x<0 and x>=0 refuted to false"
            expected actual
    ]

test_evaluableMultiOr :: [TestTree]
test_evaluableMultiOr =
    [ testCase "refutes false predicate" $ do
        let expected = MultiOr.make
                [ Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- evaluateMultiOr
            (MultiOr.make
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
        assertEqualWithExplanation "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = MultiOr.make
                [ Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
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
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
        assertEqualWithExplanation "x<0 and x>=0 refuted to false"
            expected actual
    ]

evaluatePredicate
    :: Syntax.Predicate Variable
    -> IO (Syntax.Predicate Variable)
evaluatePredicate = evaluate

evaluateConditional
    :: Pattern Variable
    -> IO (Pattern Variable)
evaluateConditional = evaluate

evaluateMultiOr
    :: MultiOr (Conditional Variable (TermLike Variable))
    -> IO (MultiOr (Conditional Variable (TermLike Variable)))
evaluateMultiOr = evaluate

evaluate
    :: SMT.Evaluator.Evaluable thing
    => thing
    -> IO thing
evaluate = Test.SMT.runSMT . evalSimplifier Mock.env . SMT.Evaluator.evaluate

