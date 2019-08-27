module Test.Kore.Step.Axiom.UserDefined
    ( test_userDefinedFunction
    , test_userDefinedFunctionSmt
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import           Data.List
                 ( sort )
import qualified Data.Map as Map

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Axiom.Concrete
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
                 ( Conditional (..), Pattern, bottom )
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeNotPredicate, makeTruePredicate )
import           Kore.Step.Axiom.UserDefined
                 ( equalityRuleEvaluator )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Kore.Step.Simplifier
                 ( mockSimplifier )
import           Test.Tasty.HUnit.Extensions

test_userDefinedFunction :: [TestTree]
test_userDefinedFunction =
    [ testCase "Applies one step" $ do
        let expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.functionalConstr11 (mkVar Mock.x)
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , remainders = OrPattern.fromPatterns []
                    }
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.functionalConstr11 (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier noSimplification)
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "f(x) => g(x)" expect actual
    , testCase "Cannot apply concrete rule to symbolic pattern" $ do
        let expect =
                AttemptedAxiom.NotApplicable
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.functionalConstr11 (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def { Attribute.concrete = Concrete True }
                    }
                )
                (mockSimplifier noSimplification)
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "f(x) => g(x)" expect actual
    , testCase "Can apply concrete rule to concrete pattern" $ do
        let expect =
                AttemptedAxiom.NotApplicable
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 Mock.a
                    , right = Mock.functionalConstr11 Mock.a
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def { Attribute.concrete = Concrete True }
                    }
                )
                (mockSimplifier noSimplification)
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "f(x) => g(x)" expect actual
    , testCase "Cannot apply step with unsat axiom pre-condition" $ do
        let expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.fromPatterns []
                    , remainders = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.functionalConstr10 (mkVar Mock.x)
                            , predicate = makeTruePredicate
                            , substitution = mempty
                             }
                        ]
                    }
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.functionalConstr11 (mkVar Mock.x)
                    , requires = makeFalsePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier noSimplification)
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "f(x) => g(x) requires false" expect actual

    , testCase "Cannot apply step with unsat condition" $ do
        let expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results =
                        OrPattern.fromPatterns [ Pattern.bottom ]
                    , remainders = OrPattern.fromPatterns []
                    }
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.functionalConstr11 (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier
                    -- Evaluate Top to Bottom.
                    (asSimplification [ (mkTop_, []) ])
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Preserves step substitution" $ do
        let expect = AttemptedAxiom.NotApplicable
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left  =
                        Mock.functionalConstr20
                            (mkVar Mock.x)
                            (mkVar Mock.x)
                    , right = Mock.g (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
                )
                (simplifierTermLike Mock.env)
                (Mock.functionalConstr20 (mkVar Mock.y) (mkVar Mock.z))
        assertEqualWithExplanation "sigma(x, x) => g(x) vs sigma(a, b)"
            expect
            actual

    -- TODO: Add a test for StepWithAxiom returning a condition.
    -- TODO: Add a test for the stepper giving up
    ]

test_userDefinedFunctionSmt :: [TestTree]
test_userDefinedFunctionSmt =
    [ testCase "Prunes results with the SMT" $ do
        let
            expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.bottom
                    , remainders = OrPattern.fromPatterns
                        [ Conditional
                            { term = baseTerm Mock.z Mock.z
                            , predicate =
                                makeNotPredicate (basePredicate Mock.z Mock.z)
                            , substitution = mempty
                            }
                        ]
                    }
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left  = baseTerm Mock.x Mock.y
                    , right = Mock.a
                    , requires = basePredicate Mock.x Mock.y
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
                )
                (simplifierTermLike Mock.env)
                (baseTerm Mock.z Mock.z)
        assertEqualWithExplanation "sigma(x,x) => bottom + sigma(x,x) remainder"
            expect
            actual

    , testCase "Prunes remainders with the SMT" $ do
        let
            expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.a
                            , predicate =
                                makeNotPredicate (basePredicate Mock.z Mock.z)
                            , substitution = mempty
                            }
                        ]
                    , remainders = OrPattern.bottom
                    }
        actual <-
            evaluateWithAxiom
                (EqualityRule RulePattern
                    { left  = baseTerm Mock.x Mock.y
                    , right = Mock.a
                    , requires = makeNotPredicate (basePredicate Mock.x Mock.y)
                    , ensures = makeTruePredicate
                    , attributes = def
                    }
                )
                (simplifierTermLike Mock.env)
                (baseTerm Mock.z Mock.z)
        assertEqualWithExplanation "sigma(x,x) => a + bottom remainder"
            expect
            actual
    ]
  where
    comparesTo0 term positive =
        makeEqualsPredicate
            (Mock.lessInt
                (Mock.fTestInt term)
                (Mock.builtinInt 0)
            )
            (Mock.builtinBool positive)
    fOfLessThan0 term = comparesTo0 term True
    fOfNotLessThan0 term = comparesTo0 term False
    basePredicate var1 var2 =
        makeAndPredicate
            (fOfLessThan0 (mkVar var1))
            (fOfNotLessThan0 (mkVar var2))
    baseTerm var1 var2 = Mock.functionalConstr20 (mkVar var1) (mkVar var2)

noSimplification :: [(TermLike Variable, [Pattern Variable])]
noSimplification = []


asSimplification
    :: [(TermLike Variable, [Pattern Variable])]
    -> [(TermLike Variable, [Pattern Variable])]
asSimplification = id

evaluateWithAxiom
    :: EqualityRule Variable
    -> TermLikeSimplifier
    -> TermLike Variable
    -> IO CommonAttemptedAxiom
evaluateWithAxiom axiom simplifier patt =
    normalizeResult <$> evaluated
  where
    normalizeResult :: CommonAttemptedAxiom -> CommonAttemptedAxiom
    normalizeResult =
        \case
            AttemptedAxiom.Applied AttemptedAxiomResults
                { results, remainders } ->
                    AttemptedAxiom.Applied AttemptedAxiomResults
                        { results = fmap sortSubstitution results
                        , remainders = fmap sortSubstitution remainders
                        }
            result -> result

    sortSubstitution Conditional {term, predicate, substitution} =
        Conditional
            { term = term
            , predicate = predicate
            , substitution = Substitution.modify sort substitution
            }
    evaluated :: IO CommonAttemptedAxiom
    evaluated =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ evalSimplifier mockEnv
        $ equalityRuleEvaluator
            axiom
            Mock.substitutionSimplifier
            simplifier
            Map.empty
            patt
    mockEnv =
        Mock.env
            { simplifierTermLike = simplifier
            , simplifierPredicate = Mock.substitutionSimplifier
            }
