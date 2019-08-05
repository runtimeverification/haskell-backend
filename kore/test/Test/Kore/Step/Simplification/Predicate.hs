module Test.Kore.Step.Simplification.Predicate
    ( test_predicateSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map

import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import           Kore.Internal.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Predicate as Conditional
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( firstFullEvaluation )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Simplification.Data hiding
                 ( runSimplifier )
import qualified Kore.Step.Simplification.Predicate as PSSimplifier
                 ( create )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
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
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.g (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
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
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkElemVar Mock.x))
                            (Mock.constr10 (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate Mock.functional00 Mock.a
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
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
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.functional00)
                        , (ElemVar Mock.y, Mock.functional01)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual

    , testCase "Merges substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a) ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.y, Mock.b)
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
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
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
                                (Mock.constr10 (mkElemVar Mock.x))
                                (Mock.f (mkElemVar Mock.y))
                            )
                            (makeEqualsPredicate
                                (Mock.f (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.y, Mock.b)
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
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
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
                                (Mock.constr10 (mkElemVar Mock.x))
                                (Mock.f (mkElemVar Mock.y))
                            )
                            (makeEqualsPredicate
                                (Mock.f (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.y, Mock.b)
                        ]
                    }
        assertEqualWithExplanation "" (MultiOr.singleton expect) actual
    ]

runSimplifier
    :: BuiltinAndAxiomSimplifierMap
    -> Predicate Variable
    -> IO (OrPredicate Variable)
runSimplifier patternSimplifierMap predicate =
    fmap MultiOr.make
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier env
    $ gather
    $ simplifier predicate
  where
    env = Mock.env { simplifierAxioms = patternSimplifierMap }
    PredicateSimplifier simplifier = PSSimplifier.create

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier]
    -> BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeEvaluator
    ::  (forall variable
        .   ( FreshVariable variable
            , SortedVariable variable
            , Unparse variable
            )
        => [(TermLike variable, TermLike variable)]
        )
    -> BuiltinAndAxiomSimplifier
makeEvaluator mapping =
    BuiltinAndAxiomSimplifier
    $ const $ const $ const $ simpleEvaluator mapping

simpleEvaluator
    ::  ( FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => [(TermLike variable, TermLike variable)]
    -> TermLike variable
    -> simplifier (AttemptedAxiom variable)
simpleEvaluator [] _ = return NotApplicable
simpleEvaluator ((from, to) : ps) patt
  | from == patt =
    return $ Applied AttemptedAxiomResults
        { results = OrPattern.fromTermLike to
        , remainders = OrPattern.bottom
        }
  | otherwise =
    simpleEvaluator ps patt
