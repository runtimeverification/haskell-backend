module Test.Kore.Step.Function.Integration (test_functionIntegration) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map

import           Data.Sup
import           Kore.AST.Pure hiding
                 ( mapVariables )
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( CommonPredicate, makeAndPredicate, makeCeilPredicate,
                 makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( builtinEvaluation, definitionEvaluation,
                 firstFullEvaluation, simplifierWithFallback )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Axiom.UserDefined
                 ( equalityRuleEvaluator )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern,
                 Predicated (Predicated) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), mapVariables )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (..), Simplifier, StepPatternSimplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplify )
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_functionIntegration :: [TestTree]
test_functionIntegration =
    [ testCase "Simple evaluation" $ do
        let expect =
                Predicated
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.g (mkVar Mock.x))
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simple evaluation (builtin branch)" $ do
        let expect =
                Predicated
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (builtinEvaluation $ axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.g (mkVar Mock.x))
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin works)"
      $ do
        let expect =
                Predicated
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (simplifierWithFallback
                        (builtinEvaluation $ axiomEvaluator
                            (Mock.functionalConstr10 (mkVar Mock.x))
                            (Mock.g (mkVar Mock.x))
                        )
                        ( axiomEvaluator
                            (Mock.functionalConstr10 (mkVar Mock.x))
                            (mkVar Mock.x)
                        )
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin fails)"
      $ do
        let expect =
                Predicated
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (simplifierWithFallback
                        (builtinEvaluation $ BuiltinAndAxiomSimplifier
                            (\_ _ _ _ _ -> notApplicableAxiomEvaluator)
                        )
                        ( axiomEvaluator
                            (Mock.functionalConstr10 (mkVar Mock.x))
                            (Mock.g (mkVar Mock.x))
                        )
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates inside functions" $ do
        let expect =
                Predicated
                    { term = Mock.functional10 (Mock.functional10 Mock.c)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    ( axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.functional10 (mkVar Mock.x))
                    )
                )
                (Mock.functionalConstr10 (Mock.functionalConstr10 Mock.c))
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates 'or'" $ do
        let expect =
                Predicated
                    { term =
                        mkOr
                            (Mock.functional10 (Mock.functional10 Mock.c))
                            (Mock.functional10 (Mock.functional10 Mock.d))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    ( axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.functional10 (mkVar Mock.x))
                    )
                )
                (Mock.functionalConstr10
                    (mkOr
                        (Mock.functionalConstr10 Mock.c)
                        (Mock.functionalConstr10 Mock.d)
                    )
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates on multiple branches" $ do
        let expect =
                Predicated
                    { term =
                        Mock.functional10
                            (Mock.functional20
                                (Mock.functional10 Mock.c)
                                (Mock.functional10 Mock.c)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    ( axiomEvaluator
                        (Mock.functionalConstr10 (mkVar Mock.x))
                        (Mock.functional10 (mkVar Mock.x))
                    )
                )
                (Mock.functionalConstr10
                    (Mock.functional20
                        (Mock.functionalConstr10 Mock.c)
                        (Mock.functionalConstr10 Mock.c)
                    )
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Returns conditions" $ do
        let expect =
                Predicated
                    { term = Mock.f Mock.d
                    , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.cId)
                    ( appliedMockEvaluator Predicated
                        { term   = Mock.d
                        , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                        , substitution = mempty
                        }
                    )
                )
                (Mock.f Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Merges conditions" $ do
        let expect =
                Predicated
                    { term = Mock.functional11 (Mock.functional20 Mock.e Mock.e)
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cg)
                            (makeCeilPredicate Mock.cf)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cId
                        , appliedMockEvaluator Predicated
                            { term = Mock.e
                            , predicate = makeCeilPredicate Mock.cg
                            , substitution = mempty
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Predicated
                            { term = Mock.e
                            , predicate = makeCeilPredicate Mock.cf
                            , substitution = mempty
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.functionalConstr10Id
                        , axiomEvaluator
                            (Mock.functionalConstr10 (mkVar Mock.x))
                            (Mock.functional11 (mkVar Mock.x))
                        )
                    ]
                )
                (Mock.functionalConstr10 (Mock.functional20 Mock.c Mock.d))
        assertEqualWithExplanation "" expect actual

    , testCase "Reevaluates user-defined function results." $ do
        let expect =
                Predicated
                    { term = Mock.f Mock.e
                    , predicate = makeEqualsPredicate (Mock.f Mock.e) Mock.e
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cId
                        , axiomEvaluator Mock.c Mock.d
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Predicated
                            { term = Mock.e
                            , predicate =
                                makeEqualsPredicate (Mock.f Mock.e) Mock.e
                            , substitution = mempty
                            }
                        )
                    ]
                )
                (Mock.f Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Merges substitutions with reevaluation ones." $ do
        let expect =
                Predicated
                    { term = Mock.f Mock.e
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [   ( Mock.var_x_1
                            , Mock.a
                            )
                        ,   ( Mock.var_z_1
                            , Mock.a
                            )
                        ]
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cId
                        , appliedMockEvaluator Predicated
                            { term = Mock.d
                            , predicate = makeTruePredicate
                            , substitution = Substitution.unsafeWrap
                                [   ( Mock.x
                                    , mkVar Mock.z
                                    )
                                ]
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Predicated
                            { term = Mock.e
                            , predicate = makeTruePredicate
                            , substitution = Substitution.unsafeWrap
                                [   ( Mock.x
                                    , Mock.a
                                    )
                                ]
                            }
                        )
                    ]
                )
                (Mock.f Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simplifies substitution-predicate." $ do
        -- Mock.plain10 below prevents:
        -- 1. unification without substitution.
        -- 2. Transforming the 'and' in an equals predicate,
        --    as it would happen for functions.
        let expect =
                Predicated
                    { term = Mock.a
                    , predicate =
                        makeCeilPredicate
                            (Mock.plain10 Mock.cf)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.var_x_1, Mock.cf), (Mock.var_y_1, Mock.b) ]
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , appliedMockEvaluator Predicated
                            { term = Mock.a
                            , predicate =
                                makeCeilPredicate
                                    (mkAnd
                                        (Mock.constr20
                                            (Mock.plain10 Mock.cf)
                                            Mock.b
                                        )
                                        (Mock.constr20
                                            (Mock.plain10 (mkVar Mock.x))
                                            (mkVar Mock.y)
                                        )
                                    )
                            , substitution =
                                Substitution.wrap [(Mock.x, Mock.cf)]
                            }
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates only simplifications." $ do
        let expect =
                Predicated
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (appliedMockEvaluator Predicated
                                { term = Mock.b
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkVar Mock.y))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Picks first matching simplification." $ do
        let expect =
                Predicated
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (firstFullEvaluation
                                [ axiomEvaluator
                                    (Mock.f (Mock.g (mkVar Mock.x)))
                                    Mock.c
                                ,  appliedMockEvaluator Predicated
                                    { term = Mock.b
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ,  appliedMockEvaluator Predicated
                                    { term = Mock.c
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkVar Mock.y))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Falls back to evaluating the definition." $ do
        let expect =
                Predicated
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (axiomEvaluator
                                (Mock.f (Mock.g (mkVar Mock.x)))
                                Mock.b
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkVar Mock.y))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Multiple definition branches." $ do
        let expect =
                Predicated
                    { term = mkOr
                        (mkAnd Mock.a (mkCeil Mock.testSort Mock.cf))
                        (mkAnd Mock.b (mkNot (mkCeil Mock.testSort Mock.cf)))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (axiomEvaluator
                                (Mock.f (Mock.g (mkVar Mock.x)))
                                Mock.c
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkVar Mock.y))
                                    Mock.a
                                    (makeCeilPredicate Mock.cf)
                                , axiom
                                    (Mock.f (mkVar Mock.y))
                                    Mock.b
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Variable expansion." $ do
        let expect =
                Predicated
                    { term = mkOr
                        (mkOr
                            (mkAnd
                                Mock.a
                                (mkEquals Mock.testSort
                                    (mkVar Mock.x) Mock.a
                                )
                            )
                            (mkAnd
                                Mock.b
                                (mkEquals Mock.testSort
                                    (mkVar Mock.x) Mock.b
                                )
                            )
                        )
                        (mkAnd
                            (Mock.f (mkVar Mock.x))
                            (mkAnd
                                (mkNot
                                    (mkEquals Mock.testSort
                                        (mkVar Mock.x) Mock.a
                                    )
                                )
                                (mkNot
                                    (mkEquals Mock.testSort
                                        (mkVar Mock.x) Mock.b
                                    )
                                )
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , definitionEvaluation
                            [ axiom
                                (Mock.f Mock.a)
                                Mock.a
                                makeTruePredicate
                            , axiom
                                (Mock.f Mock.b)
                                Mock.b
                                makeTruePredicate
                            ]
                        )
                    ]
                )
                (Mock.f (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual
    ]

axiomEvaluator
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> BuiltinAndAxiomSimplifier Object
axiomEvaluator left right =
    BuiltinAndAxiomSimplifier
        (equalityRuleEvaluator (axiom left right makeTruePredicate))

axiom
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonPredicate Object
    -> EqualityRule Object Variable
axiom left right predicate =
    EqualityRule RulePattern
        { left
        , right
        , requires = predicate
        , ensures = makeTruePredicate
        , attributes = def
        }

appliedMockEvaluator
    :: CommonExpandedPattern level -> BuiltinAndAxiomSimplifier level
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier
    $ mockEvaluator
    $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = MultiOr.make
            [Test.Kore.Step.Function.Integration.mapVariables result]
        , remainders = MultiOr.make []
        }

mapVariables
    ::  ( FreshVariable variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord (variable level)
        )
    => CommonExpandedPattern level
    -> ExpandedPattern level variable
mapVariables =
    ExpandedPattern.mapVariables $ \v ->
        fromVariable v { variableCounter = Just (Element 1) }

mockEvaluator
    :: AttemptedAxiom level variable
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> StepPattern level variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
mockEvaluator evaluation _ _ _ _ _ =
    return (evaluation, SimplificationProof)

evaluate
    :: forall level . MetaOrObject level
    => MetadataTools level StepperAttributes
    -> BuiltinAndAxiomSimplifierMap level
    -> CommonStepPattern level
    -> IO (CommonExpandedPattern level)
evaluate metadataTools functionIdToEvaluator patt =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ Pattern.simplify
        metadataTools substitutionSimplifier functionIdToEvaluator patt
  where
    substitutionSimplifier :: PredicateSubstitutionSimplifier level
    substitutionSimplifier =
        PredicateSubstitution.create
            metadataTools patternSimplifier functionIdToEvaluator
    patternSimplifier
        ::  ( MetaOrObject level )
        => StepPatternSimplifier level
    patternSimplifier = Simplifier.create metadataTools functionIdToEvaluator

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
