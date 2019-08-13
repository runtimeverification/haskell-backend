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
                 ( TermLike, mkElemVar )
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
            (mkElemVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool False)
        )
        (makeEqualsPredicate
            (mkElemVar Mock.xInt `Mock.lessInt` Mock.builtinInt 0)
            (Mock.builtinBool True)
        )

test_evaluableSyntaxPredicate :: [TestTree]
test_evaluableSyntaxPredicate =
    [ testCase "refutes false predicate" $ do
        let expected = Just False
        actual <- evaluatePredicate makeFalsePredicate
        assertEqualWithExplanation "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Just False
        actual <- evaluatePredicate contradictoryPredicate
        assertEqualWithExplanation "x<0 and x>=0 refuted to false"
            expected actual
    ]

test_evaluableConditional :: [TestTree]
test_evaluableConditional =
    [ testCase "refutes false predicate" $ do
        let expected = Just False
        actual <- evaluateConditional Conditional
            { term = Mock.a
            , predicate = makeFalsePredicate
            , substitution = mempty
            }
        assertEqualWithExplanation "false refuted to false" expected actual
    , testCase "refutes predicate" $ do
        let expected = Just False
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
    Test.SMT.runSMT . evalSimplifier Mock.env . SMT.Evaluator.filterMultiOr

evaluate
    :: SMT.Evaluator.Evaluable thing
    => thing
    -> IO (Maybe Bool)
evaluate = Test.SMT.runSMT . evalSimplifier Mock.env . SMT.Evaluator.evaluate

