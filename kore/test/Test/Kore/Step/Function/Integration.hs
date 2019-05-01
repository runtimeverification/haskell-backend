module Test.Kore.Step.Function.Integration (test_functionIntegration) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map

import           Data.Sup
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
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
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..), rulePattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..), SimplificationProof (..),
                 Simplifier, TermLikeSimplifier, evalSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Step.Simplification.TermLike as TermLike
                 ( simplify )
import           Kore.Step.TermLike
import           Kore.Syntax.Variable
                 ( SortedVariable (..) )
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
                Conditional
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
                Conditional
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
                Conditional
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
                Conditional
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
                Conditional
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
                Conditional
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
                Conditional
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
                Conditional
                    { term = Mock.f Mock.d
                    , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                mockMetadataTools
                (Map.singleton
                    (AxiomIdentifier.Application Mock.cId)
                    ( appliedMockEvaluator Conditional
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
                Conditional
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
                        , appliedMockEvaluator Conditional
                            { term = Mock.e
                            , predicate = makeCeilPredicate Mock.cg
                            , substitution = mempty
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Conditional
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
                Conditional
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
                        , appliedMockEvaluator Conditional
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
                Conditional
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
                        , appliedMockEvaluator Conditional
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
                        , appliedMockEvaluator Conditional
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
                Conditional
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
                        , appliedMockEvaluator Conditional
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
                Conditional
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
                            (appliedMockEvaluator Conditional
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
                Conditional
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
                                ,  appliedMockEvaluator Conditional
                                    { term = Mock.b
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ,  appliedMockEvaluator Conditional
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
                Conditional
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
                Conditional
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
        let equalsXA = mkEquals Mock.testSort (mkVar Mock.x) Mock.a
            equalsXB = mkEquals Mock.testSort (mkVar Mock.x) Mock.b
            expect =
                Conditional
                    { term =
                        Foldable.foldr1 mkOr
                            [ mkAnd Mock.a equalsXA
                            , mkAnd Mock.b equalsXB
                            , mkAnd (Mock.f (mkVar Mock.x))
                                $ mkAnd
                                    (mkNot equalsXA)
                                    (mkNot equalsXB)
                            ]
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
    :: TermLike Variable
    -> TermLike Variable
    -> BuiltinAndAxiomSimplifier Object
axiomEvaluator left right =
    BuiltinAndAxiomSimplifier
        (equalityRuleEvaluator (axiom left right makeTruePredicate))

axiom
    :: TermLike Variable
    -> TermLike Variable
    -> Syntax.Predicate Variable
    -> EqualityRule Object Variable
axiom left right predicate =
    EqualityRule (RulePattern.rulePattern left right) { requires = predicate }

appliedMockEvaluator
    :: Pattern Variable -> BuiltinAndAxiomSimplifier Object
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier
    $ mockEvaluator
    $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = OrPattern.fromPatterns
            [Test.Kore.Step.Function.Integration.mapVariables result]
        , remainders = OrPattern.fromPatterns []
        }

mapVariables
    ::  ( FreshVariable variable
        , SortedVariable variable
        )
    => Pattern Variable
    -> Pattern variable
mapVariables =
    Pattern.mapVariables $ \v ->
        fromVariable v { variableCounter = Just (Element 1) }

mockEvaluator
    :: AttemptedAxiom Object variable
    -> SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> TermLike variable
    -> Simplifier
        (AttemptedAxiom Object variable, SimplificationProof Object)
mockEvaluator evaluation _ _ _ _ _ =
    return (evaluation, SimplificationProof)

evaluate
    :: SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifierMap Object
    -> TermLike Variable
    -> IO (Pattern Variable)
evaluate metadataTools functionIdToEvaluator patt =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ TermLike.simplify
        metadataTools substitutionSimplifier functionIdToEvaluator patt
  where
    substitutionSimplifier :: PredicateSimplifier Object
    substitutionSimplifier =
        Predicate.create
            metadataTools patternSimplifier functionIdToEvaluator
    patternSimplifier :: TermLikeSimplifier Object
    patternSimplifier = Simplifier.create metadataTools functionIdToEvaluator

mockMetadataTools :: SmtMetadataTools StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
        Mock.smtDeclarations
