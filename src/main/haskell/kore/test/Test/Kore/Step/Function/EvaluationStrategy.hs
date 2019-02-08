module Test.Kore.Step.Function.EvaluationStrategy where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( CommonPredicate, makeAndPredicate, makeEqualsPredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (Predicated) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.Function.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), CommonAttemptedAxiom )
import           Kore.Step.Function.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Function.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Function.EvaluationStrategy
import           Kore.Step.Function.UserDefined
                 ( ruleFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
                 ( CommonStepPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier, evalSimplifier )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_definitionEvaluation :: [TestTree]
test_definitionEvaluation =
    [ testCase "Simple evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.c
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.a)]
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.functionalConstr10 (mkVar Mock.x)
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
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make []
                        , remainders = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.functionalConstr10 Mock.b
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.a)]
                                }
                            , Predicated
                                { term = Mock.g Mock.b
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.b)]
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.functionalConstr10 (mkVar Mock.x)
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
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.c
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.f Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.f Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                mockMetadataTools
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
                mockMetadataTools
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
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = Substitution.wrap
                                    [(Mock.x, Mock.b)]
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.functionalConstr10 (mkVar Mock.x)
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
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.f Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                mockMetadataTools
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
                    (AttemptedAxiomResults
                        { results = OrOfExpandedPattern.make
                            [ Predicated
                                { term = Mock.g Mock.a
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , remainders = OrOfExpandedPattern.make []
                        }
                    )
        actual <-
            evaluate
                mockMetadataTools
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
                mockMetadataTools
                (builtinEvaluation failingEvaluator)
                Mock.unitMap
            )
        )
    ]

failingEvaluator :: BuiltinAndAxiomSimplifier Object
failingEvaluator =
    BuiltinAndAxiomSimplifier
        (const $ const $ const $ const $
            return (AttemptedAxiom.NotApplicable, SimplificationProof)
        )

axiomEvaluator
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> BuiltinAndAxiomSimplifier Object
axiomEvaluator left right =
    BuiltinAndAxiomSimplifier
        (ruleFunctionEvaluator (axiom left right makeTruePredicate))

axiomEvaluatorWithRemainder
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> BuiltinAndAxiomSimplifier Object
axiomEvaluatorWithRemainder left right =
    definitionEvaluation [axiom left right makeTruePredicate]

axiom
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonPredicate Object
    -> EqualityRule Object
axiom left right predicate =
    EqualityRule RulePattern
        { left
        , right
        , requires = predicate
        , attributes = def
        }

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

evaluate
    :: forall level . MetaOrObject level
    => MetadataTools level StepperAttributes
    -> BuiltinAndAxiomSimplifier level
    -> CommonStepPattern level
    -> IO (CommonAttemptedAxiom level)
evaluate metadataTools (BuiltinAndAxiomSimplifier simplifier) patt =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ simplifier
        metadataTools substitutionSimplifier patternSimplifier patt
  where
    substitutionSimplifier :: PredicateSubstitutionSimplifier level Simplifier
    substitutionSimplifier =
        PredicateSubstitution.create metadataTools patternSimplifier
    patternSimplifier
        ::  ( MetaOrObject level
            , SortedVariable variable
            , Ord (variable level)
            , Show (variable level)
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , Unparse (variable level)
            , FreshVariable variable
            )
        => StepPatternSimplifier level variable
    patternSimplifier = Simplifier.create metadataTools Map.empty
