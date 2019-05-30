module Test.Kore.Step.Axiom.EvaluationStrategy where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map

import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
                 ( Conditional (Conditional) )
import qualified Kore.Internal.Pattern as Pattern
                 ( Conditional (..) )
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), CommonAttemptedAxiom )
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Axiom.EvaluationStrategy
import           Kore.Step.Axiom.UserDefined
                 ( equalityRuleEvaluator )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..), TermLikeSimplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Unification.Substitution as Substitution
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
                Mock.metadataTools
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
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.a)]
                                }
                            ]
                        , remainders =
                            OrPattern.fromPatterns
                            $ map (fmap mkEvaluated)
                                [ Conditional
                                    { term =
                                        Mock.functionalConstr10 (mkVar Mock.x)
                                    , predicate =
                                        makeNotPredicate
                                            (makeEqualsPredicate
                                                (mkVar Mock.x)
                                                Mock.a
                                            )
                                    , substitution = mempty
                                    }
                                ]
                        }
        actual <-
            evaluate
                Mock.metadataTools
                (definitionEvaluation
                    [ axiom
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        makeTruePredicate
                    ]
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
    , testCase "Failed evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns []
                        , remainders =
                            OrPattern.fromTermLike
                            $ mkEvaluated $ Mock.functionalConstr10 Mock.b
                        }
        actual <-
            evaluate
                Mock.metadataTools
                (definitionEvaluation
                    [ axiom
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        makeTruePredicate
                    ]
                )
                (Mock.functionalConstr10 Mock.b)
        assertEqualWithExplanation "" expect actual
    , testCase "Evaluation with multiple branches" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.a)]
                                }
                            , Conditional
                                { term = Mock.g Mock.b
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.b)]
                                }
                            ]
                        , remainders =
                            OrPattern.fromPatterns
                            $ map (fmap mkEvaluated)
                                [ Conditional
                                    { term =
                                        Mock.functionalConstr10 (mkVar Mock.x)
                                    , predicate = makeAndPredicate
                                        (makeNotPredicate
                                            (makeEqualsPredicate
                                                (mkVar Mock.x)
                                                Mock.a
                                            )
                                        )
                                        (makeNotPredicate
                                            (makeEqualsPredicate
                                                (mkVar Mock.x)
                                                Mock.b
                                            )
                                        )
                                    , substitution = mempty
                                    }
                                ]
                        }
        actual <-
            evaluate
                Mock.metadataTools
                (definitionEvaluation
                    [ axiom
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        makeTruePredicate
                    , axiom
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.b)
                        makeTruePredicate
                    ]
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
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
                Mock.metadataTools
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
                Mock.metadataTools
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
                Mock.metadataTools
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
                Mock.metadataTools
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
    , testCase "Error when not fully rewriting"
        (assertErrorIO
            (assertSubstring ""
                "Unexpected simplification result with remainder"
            )
            (evaluate
                Mock.metadataTools
                (firstFullEvaluation
                    [ axiomEvaluatorWithRemainder
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                    ]
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
            )
        )
    , testCase "Error with multiple results"
        (assertErrorIO
            (assertSubstring ""
                (  "Unexpected simplification result with more than one "
                ++ "configuration"
                )
            )
            (evaluate
                Mock.metadataTools
                (firstFullEvaluation
                    [ definitionEvaluation
                        [ axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.f Mock.a)
                            makeTruePredicate
                        , axiom
                            (Mock.functionalConstr10 (mkVar Mock.x))
                            (Mock.g Mock.b)
                            makeTruePredicate
                        ]
                    ]
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
            )
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
                Mock.metadataTools
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
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.b)]
                                }
                            ]
                        , remainders =
                            OrPattern.fromPatterns
                            $ map (fmap mkEvaluated)
                                [ Conditional
                                    { term =
                                        Mock.functionalConstr10 (mkVar Mock.x)
                                    , predicate =
                                        makeNotPredicate
                                            (makeEqualsPredicate
                                                (mkVar Mock.x)
                                                Mock.b
                                            )
                                    , substitution = mempty
                                    }
                                ]
                        }
        actual <-
            evaluate
                Mock.metadataTools
                (simplifierWithFallback
                    (axiomEvaluatorWithRemainder
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                    )
                    (axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.f Mock.a)
                    )
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
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
                Mock.metadataTools
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
                Mock.metadataTools
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
                Mock.metadataTools
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
                "Expecting hook MAP.unit to reduce concrete pattern"
            )
            (evaluate
                Mock.metadataTools
                (builtinEvaluation failingEvaluator)
                Mock.unitMap
            )
        )
    ]

failingEvaluator :: BuiltinAndAxiomSimplifier
failingEvaluator =
    BuiltinAndAxiomSimplifier $ \_ _ _ _ _ ->
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
    :: SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifier
    -> TermLike Variable
    -> IO (CommonAttemptedAxiom)
evaluate metadataTools (BuiltinAndAxiomSimplifier simplifier) patt =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier
    $ simplifier
        metadataTools substitutionSimplifier patternSimplifier Map.empty patt
  where
    substitutionSimplifier :: PredicateSimplifier
    substitutionSimplifier =
        Predicate.create metadataTools patternSimplifier Map.empty
    patternSimplifier :: TermLikeSimplifier
    patternSimplifier = Simplifier.create metadataTools Map.empty
