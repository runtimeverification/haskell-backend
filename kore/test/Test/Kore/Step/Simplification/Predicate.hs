module Test.Kore.Step.Simplification.Predicate
    ( test_predicateSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
import           Kore.Step.Axiom.EvaluationStrategy
                 ( firstFullEvaluation )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.OrPredicate
                 ( OrPredicate )
import           Kore.Step.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Step.Predicate as Conditional
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Simplification.Data hiding
                 ( runSimplifier )
import qualified Kore.Step.Simplification.Predicate as PSSimplifier
                 ( create )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.TermLike
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_predicateSimplification :: [TestTree]
test_predicateSimplification =
    [ testCase "Identity for top and bottom" $ do
        actualBottom <- runSimplifier Map.empty Conditional.bottomPredicate
        assertEqualWithExplanation "" mempty actualBottom
        actualTop <- runSimplifier Map.empty Conditional.topPredicate
        assertEqualWithExplanation ""
            (MultiOr.singleton Conditional.topPredicate)
            actualTop

    , testCase "Applies substitution to predicate" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f Mock.a)
                            (Mock.g Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkVar Mock.x))
                            (Mock.g (mkVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.a)
                        , (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            Mock.functional00
                            Mock.functional01
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkVar Mock.x))
                            (Mock.constr10 (mkVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate Mock.functional00 Mock.a
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                    [   ( Mock.f Mock.functional00
                                        , Mock.functional00
                                        )
                                , (Mock.f Mock.functional01, Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkVar Mock.x))
                            (Mock.f (mkVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.functional00)
                        , (Mock.y, Mock.functional01)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Merges substitution from predicate simplification" $ do
        let expect =
                Conditional
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
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkVar Mock.x))
                            (Mock.f (mkVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Reapplies substitution from predicate simplification" $ do
        let expect =
                Conditional
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
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
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
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Simplifies after reapplying substitution" $ do
        let expect =
                Conditional
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
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                , (Mock.f Mock.a, Mock.g Mock.b)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
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
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual
    ]

mockMetadataTools :: SmtMetadataTools StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
        Mock.smtDeclarations

runSimplifier
    :: BuiltinAndAxiomSimplifierMap
    -> Predicate Variable
    -> IO (OrPredicate Variable)
runSimplifier patternSimplifierMap predicate =
    fmap MultiOr.make
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ gather
    $ simplifier predicate
  where
    PredicateSimplifier simplifier =
        PSSimplifier.create
            mockMetadataTools
            (Simplifier.create mockMetadataTools patternSimplifierMap)
            patternSimplifierMap

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier]
    -> BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeEvaluator
    ::  (forall variable
        .   ( FreshVariable variable
            , SortedVariable variable
            )
        => [(TermLike variable, TermLike variable)]
        )
    -> BuiltinAndAxiomSimplifier
makeEvaluator mapping =
    BuiltinAndAxiomSimplifier
        $ const $ const $ const $ const $ simpleEvaluator mapping

simpleEvaluator
    ::  ( FreshVariable variable
        , SortedVariable variable
        )
    => [(TermLike variable, TermLike variable)]
    -> TermLike variable
    -> Simplifier (AttemptedAxiom variable)
simpleEvaluator [] _ = return NotApplicable
simpleEvaluator ((from, to) : ps) patt
  | from == patt =
    return $ Applied AttemptedAxiomResults
        { results = OrPattern.fromTermLike to
        , remainders = OrPattern.bottom
        }
  | otherwise =
    simpleEvaluator ps patt
