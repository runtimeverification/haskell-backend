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

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Axiom.Concrete
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
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
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern, Predicated (..), bottom )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), StepPatternSimplifier,
                 evalSimplifier )
import           Kore.Step.StepperAttributes
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
                    { results = OrOfExpandedPattern.make
                        [ Predicated
                            { term = Mock.functionalConstr11 (mkVar Mock.x)
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , remainders = OrOfExpandedPattern.make []
                    }
        actual <-
            evaluateWithAxiom
                mockMetadataTools
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.functionalConstr11 (mkVar Mock.x)
                    , requires = makeTruePredicate
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
                    , attributes = def { Attribute.concrete = Concrete True }
                    }
                )
                (mockSimplifier noSimplification)
                (Mock.functionalConstr10 (mkVar Mock.x))
        assertEqualWithExplanation "f(x) => g(x)" expect actual
    , testCase "Cannot apply step with unsat axiom pre-condition" $ do
        let expect =
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = OrOfExpandedPattern.make []
                    , remainders = OrOfExpandedPattern.make
                        [ Predicated
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
                        OrOfExpandedPattern.make [ ExpandedPattern.bottom ]
                    , remainders = OrOfExpandedPattern.make []
                    }
        actual <-
            evaluateWithAxiom
                mockMetadataTools
                (EqualityRule RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.functionalConstr11 (mkVar Mock.x)
                    , requires = makeTruePredicate
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
                    { results = OrOfExpandedPattern.make
                        [ Predicated
                            { term = Mock.g (mkVar Mock.z)
                            , predicate = makeTruePredicate
                            , substitution = Substitution.wrap
                                [(Mock.y, mkVar Mock.z)]
                            }
                        ]
                    , remainders = OrOfExpandedPattern.make
                        [ Predicated
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
    ::  [   ( StepPattern level Variable
            , ([ExpandedPattern level Variable], SimplificationProof level)
            )
        ]
noSimplification = []


asSimplification
    ::  [   ( StepPattern level Variable
            , ([ExpandedPattern level Variable], SimplificationProof level)
            )
        ]
    ->  [   ( StepPattern level Variable
            , ([ExpandedPattern level Variable], SimplificationProof level)
            )
        ]
asSimplification = id

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

evaluateWithAxiom
    :: forall level . MetaOrObject level
    => MetadataTools level StepperAttributes
    -> EqualityRule level Variable
    -> StepPatternSimplifier level
    -> CommonStepPattern level
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

    sortSubstitution Predicated {term, predicate, substitution} =
        Predicated
            { term = term
            , predicate = predicate
            , substitution = Substitution.modify sort substitution
            }
    evaluated :: IO (CommonAttemptedAxiom level)
    evaluated =
        (<$>) fst
        $ SMT.runSMT SMT.defaultConfig
        $ evalSimplifier emptyLogger noRepl
        $ equalityRuleEvaluator
            axiom
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
            Map.empty
            patt
