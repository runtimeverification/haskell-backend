module Test.Kore.Step.Axiom.UserDefined (test_userDefinedFunction) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import           Data.List
                 ( sort )
import qualified Data.Map as Map

import           Kore.AST.Valid
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Axiom.Concrete
import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeFalsePredicate, makeNotPredicate,
                 makeTruePredicate )
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 CommonAttemptedAxiom )
import qualified Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Axiom.UserDefined
                 ( equalityRuleEvaluator )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
                 ( Conditional (..), Pattern, bottom )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), TermLikeSimplifier,
                 evalSimplifier )
import           Kore.Step.TermLike
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
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
                mockMetadataTools
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
                mockMetadataTools
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
                mockMetadataTools
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
                mockMetadataTools
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
                mockMetadataTools
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
                    (asSimplification [ (mkTop_, ([], SimplificationProof)) ])
                )
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Preserves step substitution" $ do
        let expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.g (mkVar Mock.z)
                            , predicate = makeTruePredicate
                            , substitution = Substitution.wrap
                                [(Mock.y, mkVar Mock.z)]
                            }
                        ]
                    , remainders = OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.functionalConstr20
                                (mkVar Mock.y)
                                (mkVar Mock.z)
                            , predicate =
                                makeNotPredicate
                                    (makeEqualsPredicate
                                        (mkVar Mock.y) (mkVar Mock.z)
                                    )
                            , substitution = mempty
                            }
                        ]
                    }
        actual <-
            evaluateWithAxiom
                mockMetadataTools
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
                (mockSimplifier noSimplification)
                (Mock.functionalConstr20
                    (mkVar Mock.y)
                    (mkVar Mock.z)
                )
        assertEqualWithExplanation "sigma(x,x) => g(x) vs sigma(a, b)"
            expect
            actual

    -- TODO: Add a test for StepWithAxiom returning a condition.
    -- TODO: Add a test for the stepper giving up
    ]

noSimplification
    ::  [   ( TermLike Variable
            , ([Pattern level Variable], SimplificationProof level)
            )
        ]
noSimplification = []


asSimplification
    ::  [   ( TermLike Variable
            , ([Pattern level Variable], SimplificationProof level)
            )
        ]
    ->  [   ( TermLike Variable
            , ([Pattern level Variable], SimplificationProof level)
            )
        ]
asSimplification = id

mockMetadataTools :: SmtMetadataTools StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
        Mock.smtDeclarations

evaluateWithAxiom
    :: forall level . MetaOrObject level
    => SmtMetadataTools StepperAttributes
    -> EqualityRule level Variable
    -> TermLikeSimplifier level
    -> TermLike Variable
    -> IO (CommonAttemptedAxiom level)
evaluateWithAxiom
    metadataTools
    axiom
    simplifier
    patt
  = do
    results <- evaluated
    return (normalizeResult results)
  where
    normalizeResult
        :: CommonAttemptedAxiom level -> CommonAttemptedAxiom level
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
    evaluated :: IO (CommonAttemptedAxiom level)
    evaluated =
        (<$>) fst
        $ SMT.runSMT SMT.defaultConfig
        $ evalSimplifier emptyLogger
        $ equalityRuleEvaluator
            axiom
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
            Map.empty
            patt
