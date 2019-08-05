module Test.Kore.Step.Axiom.EvaluationStrategy where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Axiom.Concrete as Attribute
                 ( Concrete (Concrete) )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
                 ( Conditional (Conditional) )
import qualified Kore.Internal.Pattern as Pattern
                 ( Conditional (..) )
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( Predicate, makeEqualsPredicate, makeNotPredicate,
                 makeTruePredicate )
import           Kore.Step.Axiom.EvaluationStrategy
import           Kore.Step.Axiom.UserDefined
                 ( equalityRuleEvaluator )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.Simplification.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), CommonAttemptedAxiom,
                 evalSimplifier )
import qualified Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_definitionEvaluation :: [TestTree]
test_definitionEvaluation =
    [ testCase "Simple evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.c
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (definitionEvaluation
                    [ axiom
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.g (mkVar Mock.x))
                        makeTruePredicate
                    ]
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual
    , testCase "Evaluation with remainder" $ do
        let requirement = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
            expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results =
                        OrPattern.fromPattern Conditional
                            { term = Mock.g Mock.a
                            , predicate = requirement
                            , substitution = mempty
                            }
                    , remainders =
                        OrPattern.fromPatterns
                        $ map (fmap mkEvaluated)
                            [ Conditional
                                { term = Mock.functionalConstr10 Mock.a
                                , predicate = makeNotPredicate requirement
                                , substitution = mempty
                                }
                            ]
                    }
        actual <-
            evaluate
                (definitionEvaluation
                    [ axiom
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        requirement
                    ]
                )
                (Mock.functionalConstr10 Mock.a)
        assertEqualWithExplanation "" expect actual
    , testCase "Failed evaluation" $ do
        let expect = AttemptedAxiom.NotApplicable
        actual <-
            evaluate
                (definitionEvaluation
                    [ axiom
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        makeTruePredicate
                    ]
                )
                (Mock.functionalConstr10 Mock.b)
        assertEqualWithExplanation "" expect actual
    , testCase "Evaluation with multiple branches SMT prunes remainders" $ do
        let initial = Mock.functionalConstr10 Mock.a
            final1 = Mock.g Mock.a
            final2 = Mock.g Mock.b
            requirement1 = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
            requirement2 = makeNotPredicate requirement1
            axiom1 = axiom initial final1 requirement1
            axiom2 = axiom initial final2 requirement2
            evaluator = definitionEvaluation [axiom1, axiom2]
            expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.fromPatterns
                        [ Conditional
                            { term = final1
                            , predicate = requirement1
                            , substitution = mempty
                            }
                        , Conditional
                            { term = final2
                            , predicate = requirement2
                            , substitution = mempty
                            }
                        ]
                    , remainders = OrPattern.bottom
                    }
        actual <- evaluate evaluator initial
        assertEqualWithExplanation "" expect actual
    , testCase "Does not evaluate concrete axiom with symbolic input" $ do
        let expectConcrete =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromTermLike (Mock.g Mock.c)
                        , remainders = OrPattern.fromPatterns []
                        }

            symbolicTerm = Mock.functionalConstr10 (mkVar Mock.y)
            expectSymbolic = AttemptedAxiom.NotApplicable

            evaluator = definitionEvaluation
                [ EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.g (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                        { Attribute.Axiom.concrete = Attribute.Concrete True }
                    }
                ]

        actualConcrete <- evaluate evaluator (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expectConcrete actualConcrete

        actualSymbolic <- evaluate evaluator symbolicTerm
        assertEqualWithExplanation "" expectSymbolic actualSymbolic
    ]

test_firstFullEvaluation :: [TestTree]
test_firstFullEvaluation =
    [ testCase "Simple evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.c
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (firstFullEvaluation
                    [ axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.g (mkVar Mock.x))
                    ]
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual
    , testCase "Uses first matching" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.f Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (firstFullEvaluation
                    [ axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                    , axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.f Mock.a)
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    ]
                )
                (Mock.functionalConstr10 Mock.a)
        assertEqualWithExplanation "" expect actual
    , testCase "Skips partial matches" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.f Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (firstFullEvaluation
                    [ axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    , axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.f Mock.a)
                    ]
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
    , testCase "None matching" $ do
        let
            expect = AttemptedAxiom.NotApplicable
        actual <-
            evaluate
                (firstFullEvaluation
                    [ axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    ]
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
    , testCase "Error when not fully rewriting" $ do
        let requirement = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
        assertErrorIO
            (assertSubstring ""
                "Unexpected simplification result with remainder"
            )
            (evaluate
                (firstFullEvaluation
                    [ definitionEvaluation
                        [ axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.g Mock.a)
                            requirement
                        ]
                    ]
                )
                (Mock.functionalConstr10 Mock.a)
            )
    , testCase "Error with multiple results" $ do
        let requirement = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
        assertErrorIO
            (assertSubstring ""
                (  "Unexpected simplification result with more than one "
                ++ "configuration"
                )
            )
            (evaluate
                (firstFullEvaluation
                    [ definitionEvaluation
                        [ axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.g Mock.a)
                            requirement
                        , axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.g Mock.b)
                            (makeNotPredicate requirement)
                        ]
                    ]
                )
                (Mock.functionalConstr10 Mock.a)
            )
    ]

test_simplifierWithFallback :: [TestTree]
test_simplifierWithFallback =
    [ testCase "Uses first" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (simplifierWithFallback
                    (axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    )
                    (axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.f Mock.a)
                    )
                )
                (Mock.functionalConstr10 Mock.a)
        assertEqualWithExplanation "" expect actual
    , testCase "Uses first with remainder" $ do
        let requirement = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
            expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.g Mock.a
                            , predicate = requirement
                            , substitution = mempty
                            }
                        ]
                    , remainders =
                        OrPattern.fromPatterns $ (map . fmap) mkEvaluated
                            [ Conditional
                                { term = Mock.functionalConstr10 Mock.a
                                , predicate = makeNotPredicate requirement
                                , substitution = mempty
                                }
                            ]
                    }
        actual <-
            evaluate
                (simplifierWithFallback
                    (definitionEvaluation
                        [ axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.g Mock.a)
                            requirement
                        ]
                    )
                    (definitionEvaluation
                        [ axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.f Mock.a)
                            (makeNotPredicate requirement)
                        ]
                    )
                )
                (Mock.functionalConstr10 Mock.a)
        assertEqualWithExplanation "" expect actual
    , testCase "Falls back to second" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.f Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (simplifierWithFallback
                    (axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    )
                    (axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.f Mock.a)
                    )
                )
                (Mock.functionalConstr10 Mock.b)
        assertEqualWithExplanation "" expect actual
    , testCase "None works" $ do
        let
            expect = AttemptedAxiom.NotApplicable
        actual <-
            evaluate
                (simplifierWithFallback
                    (axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    )
                    (axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.f Mock.a)
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual
    ]

test_builtinEvaluation :: [TestTree]
test_builtinEvaluation =
    [ testCase "Simple evaluation" $ do
        let
            expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
        actual <-
            evaluate
                (builtinEvaluation
                    (axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                    )
                )
                (Mock.functionalConstr10 Mock.a)
        assertEqualWithExplanation "" expect actual
    , testCase "Failed evaluation"
        (assertErrorIO
            (assertSubstring ""
                "Expecting hook 'MAP.unit' to reduce concrete pattern"
            )
            (evaluate
                (builtinEvaluation failingEvaluator)
                Mock.unitMap
            )
        )
    ]

failingEvaluator :: BuiltinAndAxiomSimplifier
failingEvaluator =
    BuiltinAndAxiomSimplifier $ \_ _ _ _ ->
        return AttemptedAxiom.NotApplicable

axiomEvaluator
    :: TermLike Variable
    -> TermLike Variable
    -> BuiltinAndAxiomSimplifier
axiomEvaluator left right =
    BuiltinAndAxiomSimplifier
        (equalityRuleEvaluator (axiom left right makeTruePredicate))

axiomEvaluatorWithRemainder
    :: TermLike Variable
    -> TermLike Variable
    -> BuiltinAndAxiomSimplifier
axiomEvaluatorWithRemainder left right =
    definitionEvaluation [axiom left right makeTruePredicate]

axiom
    :: TermLike Variable
    -> TermLike Variable
    -> Predicate Variable
    -> EqualityRule Variable
axiom left right predicate =
    EqualityRule RulePattern
        { left
        , right
        , requires = predicate
        , ensures = makeTruePredicate
        , attributes = def
        }

evaluate
    :: BuiltinAndAxiomSimplifier
    -> TermLike Variable
    -> IO CommonAttemptedAxiom
evaluate (BuiltinAndAxiomSimplifier simplifier) patt =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier Mock.env
    $ simplifier substitutionSimplifier patternSimplifier Map.empty patt
  where
    substitutionSimplifier = Predicate.create
    patternSimplifier = Simplifier.create
