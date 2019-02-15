module Test.Kore.Step.Simplification.PredicateSubstitution
    ( test_predicateSubstitutionSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonPredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Function.Data
import           Kore.Step.Function.EvaluationStrategy
                 ( firstFullEvaluation )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (SimplificationProof), Simplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.PredicateSubstitution as PSSimplifier
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_predicateSubstitutionSimplification :: [TestTree]
test_predicateSubstitutionSimplification =
    [ testCase "Identity for top and bottom" $ do
        actualBottom <- runSimplifier Map.empty Predicated.bottomPredicate
        assertEqualWithExplanation ""
            Predicated.bottomPredicate
            actualBottom
        actualTop <- runSimplifier Map.empty Predicated.topPredicate
        assertEqualWithExplanation ""
            Predicated.topPredicate
            actualTop

    , testCase "Applies substitution to predicate" $ do
        let expect =
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f Mock.a)
                            (Mock.g Mock.b)
                    , substitution = Substitution.wrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkVar Mock.x))
                            (Mock.g (mkVar Mock.y))
                    , substitution = Substitution.wrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            Mock.functional00
                            Mock.functional01
                    , substitution = Substitution.wrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkVar Mock.x))
                            (Mock.constr10 (mkVar Mock.y))
                    , substitution = Substitution.wrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Predicated
                    { term = ()
                    , predicate = makeEqualsPredicate Mock.functional00 Mock.a
                    , substitution = Substitution.wrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                    [ (Mock.f Mock.functional00, Mock.functional00)
                                , (Mock.f Mock.functional01, Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkVar Mock.x))
                            (Mock.f (mkVar Mock.y))
                    , substitution = Substitution.wrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "Merges substitution from predicate simplification" $ do
        let expect =
                Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkVar Mock.x))
                            (Mock.f (mkVar Mock.y))
                    , substitution = Substitution.wrap
                        [ (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "Reapplies substitution from predicate simplification" $ do
        let expect =
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f Mock.a)
                            (Mock.g Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Predicated
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate
                                (Mock.constr10 (mkVar Mock.x))
                                (Mock.f (mkVar Mock.y))
                            )
                            (makeEqualsPredicate
                                (Mock.f (mkVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.wrap
                        [ (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" expect actual

    , testCase "Simplifies after reapplying substitution" $ do
        let expect =
                Predicated
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.g Mock.b)
                            (Mock.g Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                , (Mock.f Mock.a, Mock.g Mock.b)
                                ]
                            ]
                        )
                    ]
                )
                Predicated
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate
                                (Mock.constr10 (mkVar Mock.x))
                                (Mock.f (mkVar Mock.y))
                            )
                            (makeEqualsPredicate
                                (Mock.f (mkVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.wrap
                        [ (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" expect actual
    ]

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

runSimplifier
    :: BuiltinAndAxiomSimplifierMap Object
    -> CommonPredicateSubstitution Object
    -> IO (CommonPredicateSubstitution Object)
runSimplifier patternSimplifierMap predicateSubstitution =
    case simplifier of
        (PredicateSubstitutionSimplifier unwrapped) ->
            (<$>) fst
            $ SMT.runSMT SMT.defaultConfig
            $ evalSimplifier mempty
            $ unwrapped predicateSubstitution
  where
    simplifier =
        PSSimplifier.create
            mockMetadataTools
            (Simplifier.create mockMetadataTools patternSimplifierMap)

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier Object]
    -> BuiltinAndAxiomSimplifier Object
simplificationEvaluator = firstFullEvaluation

makeEvaluator
    ::  (forall variable
        .   ( FreshVariable variable
            , OrdMetaOrObject variable
            , SortedVariable variable
            , ShowMetaOrObject variable
            )
        => [(StepPattern Object variable, StepPattern Object variable)]
        )
    -> BuiltinAndAxiomSimplifier Object
makeEvaluator mapping =
    BuiltinAndAxiomSimplifier
        $ const $ const $ const $ simpleEvaluator mapping

simpleEvaluator
    ::  ( FreshVariable variable
        , OrdMetaOrObject variable
        , SortedVariable variable
        , ShowMetaOrObject variable
        )
    => [(StepPattern Object variable, StepPattern Object variable)]
    -> StepPattern Object variable
    -> Simplifier
        ( AttemptedAxiom Object variable
        , SimplificationProof Object
        )
simpleEvaluator [] _ = return (NotApplicable, SimplificationProof)
simpleEvaluator ((from, to) : ps) patt
  | from == patt =
    return
        ( Applied AttemptedAxiomResults
            { results = OrOfExpandedPattern.make [Predicated.fromPurePattern to]
            , remainders = OrOfExpandedPattern.make []
            }
        , SimplificationProof
        )
  | otherwise =
    simpleEvaluator ps patt

