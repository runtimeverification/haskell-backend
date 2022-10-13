module Test.Kore.Rewrite.Axiom.EvaluationStrategy (
    test_simplificationEvaluation,
    test_applyFirstSimplifierThatWorks,
    test_builtinEvaluation,
) where

import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern as Pattern (
    Conditional (Conditional),
 )
import Kore.Internal.Pattern qualified as Pattern (
    Conditional (..),
 )
import Kore.Internal.Predicate (
    Predicate,
    makeEqualsPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.EvaluationStrategy
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify
import Kore.Simplify.Simplify qualified as AttemptedAxiom (
    AttemptedAxiom (..),
 )
import Prelude.Kore
import Test.Kore.Equation.Common (
    axiom,
    axiom_,
    concrete,
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplificationEvaluation :: [TestTree]
test_simplificationEvaluation =
    [ testCase "Simple evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
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
                ( simplificationEvaluation $
                    axiom
                        (Mock.functionalConstr10 (mkElemVar Mock.xConfig))
                        (Mock.g (mkElemVar Mock.xConfig))
                        makeTruePredicate
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqual "" expect actual
    , testCase "Failed evaluation" $ do
        let expect = AttemptedAxiom.NotApplicable
        actual <-
            evaluate
                ( simplificationEvaluation $
                    axiom
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        makeTruePredicate
                )
                (Mock.functionalConstr10 Mock.b)
        assertEqual "" expect actual
    , testCase "Does not evaluate concrete axiom with symbolic input" $ do
        let expectConcrete =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromTermLike
                                (Mock.g Mock.c)
                        , remainders = OrPattern.fromPatterns []
                        }

            symbolicTerm = Mock.functionalConstr10 (mkElemVar Mock.yConfig)
            expectSymbolic = AttemptedAxiom.NotApplicable

            evaluator =
                simplificationEvaluation $
                    axiom_
                        (Mock.functionalConstr10 (mkElemVar Mock.xConfig))
                        (Mock.g (mkElemVar Mock.xConfig))
                        & concrete [mkElemVar Mock.xConfig]

        actualConcrete <- evaluate evaluator (Mock.functionalConstr10 Mock.c)
        assertEqual "" expectConcrete actualConcrete

        actualSymbolic <- evaluate evaluator symbolicTerm
        assertEqual "" expectSymbolic actualSymbolic
    ]

test_applyFirstSimplifierThatWorks :: [TestTree]
test_applyFirstSimplifierThatWorks =
    [ testCase "Simple evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.g Mock.c
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let c = Mock.functionalConstr10 Mock.c
        actual <-
            evaluate
                ( applyFirstSimplifierThatWorks
                    [ axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.xConfig))
                        (Mock.g (mkElemVar Mock.xConfig))
                        c
                        trueSideCondition
                    ]
                )
                c
        assertEqual "" expect actual
    , testCase "Uses first matching" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.f Mock.a
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let a = Mock.functionalConstr10 Mock.a
        actual <-
            evaluate
                ( applyFirstSimplifierThatWorks
                    [ axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                        a
                        trueSideCondition
                    , axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.xConfig))
                        (Mock.f Mock.a)
                        a
                        trueSideCondition
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        a
                        trueSideCondition
                    ]
                )
                a
        assertEqual "" expect actual
    , testCase "Skips partial matches" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.f Mock.a
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let xConfig = Mock.functionalConstr10 (mkElemVar Mock.xConfig)
        actual <-
            evaluate
                ( applyFirstSimplifierThatWorks
                    [ axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                        xConfig
                        trueSideCondition
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        xConfig
                        trueSideCondition
                    , axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.xConfig))
                        (Mock.f Mock.a)
                        xConfig
                        trueSideCondition
                    ]
                )
                xConfig
        assertEqual "" expect actual
    , testCase "None matching" $ do
        let expect = AttemptedAxiom.NotApplicable
        let xConfig = Mock.functionalConstr10 (mkElemVar Mock.xConfig)
        actual <-
            evaluate
                ( applyFirstSimplifierThatWorks
                    [ axiomEvaluator
                        (Mock.functionalConstr10 Mock.b)
                        (Mock.g Mock.a)
                        xConfig
                        trueSideCondition
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.a)
                        xConfig
                        trueSideCondition
                    ]
                )
                xConfig
        assertEqual "" expect actual
    , testCase "Skip when remainder" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.g Mock.b
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let requirement = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
        let a = Mock.functionalConstr10 Mock.a
        actual <-
            evaluate
                ( applyFirstSimplifierThatWorks
                    [ simplificationEvaluation
                        ( axiom
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.g Mock.a)
                            requirement
                        )
                        a
                        trueSideCondition
                    , axiomEvaluator
                        (Mock.functionalConstr10 Mock.a)
                        (Mock.g Mock.b)
                        a
                        trueSideCondition
                    ]
                )
                a
        assertEqual "" expect actual
    , testCase "Apply with top configuration" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f Mock.a)
                    (Mock.g Mock.b)
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.g Mock.a
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let a = Mock.functionalConstr10 Mock.a
        actual <-
            evaluateWithPredicate
                ( applyFirstSimplifierThatWorks
                    [ axiomEvaluatorWithRequires
                        a
                        (Mock.g Mock.a)
                        requirement
                        a
                        (SideCondition.fromPredicateWithReplacements requirement)
                    , axiomEvaluator
                        a
                        (Mock.g Mock.b)
                        a
                        (SideCondition.fromPredicateWithReplacements requirement)
                    ]
                )
                a
                requirement
        assertEqual "" expect actual
    , testCase "Don't apply due to top configuration" $ do
        let requirement = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
        let not_requirement = makeNotPredicate requirement
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.g Mock.b
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let a = Mock.functionalConstr10 Mock.a
        actual <-
            evaluateWithPredicate
                ( applyFirstSimplifierThatWorks
                    [ axiomEvaluatorWithRequires
                        a
                        (Mock.g Mock.a)
                        requirement
                        a
                        (SideCondition.fromPredicateWithReplacements not_requirement)
                    , axiomEvaluator
                        a
                        (Mock.g Mock.b)
                        a
                        (SideCondition.fromPredicateWithReplacements not_requirement)
                    ]
                )
                a
                not_requirement
        assertEqual "" expect actual
    ]

test_builtinEvaluation :: [TestTree]
test_builtinEvaluation =
    [ testCase "Simple evaluation" $ do
        let expect =
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results =
                            OrPattern.fromPatterns
                                [ Conditional
                                    { term = Mock.g Mock.a
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                        , remainders = OrPattern.fromPatterns []
                        }
        let a = Mock.functionalConstr10 Mock.a
        actual <-
            evaluate
                ( const
                    . builtinEvaluation
                        ( axiomEvaluator
                            (Mock.functionalConstr10 Mock.a)
                            (Mock.g Mock.a)
                            a
                            trueSideCondition
                        )
                )
                a
        assertEqual "" expect actual
    , testCase
        "Failed evaluation"
        ( assertErrorIO
            ( assertSubstring
                ""
                "Expecting hook 'MAP.unit' to reduce concrete pattern"
            )
            ( evaluate
                (const . builtinEvaluation (failingEvaluator Mock.unitMap trueSideCondition))
                Mock.unitMap
            )
        )
    ]

trueSideCondition :: SideCondition RewritingVariableName
trueSideCondition = SideCondition.fromPredicateWithReplacements makeTruePredicate

failingEvaluator ::
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    Simplifier (AttemptedAxiom RewritingVariableName)
failingEvaluator _ _ = return AttemptedAxiom.NotApplicable

axiomEvaluatorWithRequires ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    Simplifier (AttemptedAxiom RewritingVariableName)
axiomEvaluatorWithRequires left right requires =
    simplificationEvaluation (axiom left right requires)

axiomEvaluator ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    Simplifier (AttemptedAxiom RewritingVariableName)
axiomEvaluator left right =
    simplificationEvaluation (axiom left right makeTruePredicate)

evaluate ::
    ( TermLike RewritingVariableName ->
      SideCondition RewritingVariableName ->
      Simplifier (AttemptedAxiom RewritingVariableName)
    ) ->
    TermLike RewritingVariableName ->
    IO CommonAttemptedAxiom
evaluate simplifier term =
    evaluateWithPredicate simplifier term makeTruePredicate

evaluateWithPredicate ::
    ( TermLike RewritingVariableName ->
      SideCondition RewritingVariableName ->
      Simplifier (AttemptedAxiom RewritingVariableName)
    ) ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName ->
    IO CommonAttemptedAxiom
evaluateWithPredicate simplifier term predicate =
    runSimplifierSMT Mock.env $
        simplifier
            term
            (SideCondition.fromPredicateWithReplacements predicate)
