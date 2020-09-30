module Test.Kore.Reachability.AllPathClaim
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Data.Foldable as Foldable

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate_
    , makeNotPredicate
    )
import Kore.Internal.TermLike
    ( mkAnd
    , mkDefined
    , mkElemVar
    , mkEquals
    , mkOr
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability
    ( AllPathClaim (..)
    , mkAllPathClaim
    , simplify
    )
import Kore.Rewriting.RewritingVariable
    ( mkRuleVariable
    )
import Kore.Step.Simplification.Data
    ( runSimplifier
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SMT
    ( runSMT
    )
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testCase "already simplified" $ do
        let claim =
                mkAllPathClaim
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike Mock.b)
            expect = [claim]
        actual <- runSimpl claim
        assertEqual "" expect actual

    , testGroup "simplifies left-hand side"

        [ testCase "simplifies left-hand term" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike
                            (mkAnd
                                Mock.a
                                (mkEquals Mock.testSort Mock.a Mock.a)
                            )
                        )
                        []
                        (OrPattern.fromTermLike Mock.b)
                expect =
                    [ mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike Mock.b)
                    ]
            actual <- runSimpl claim
            assertEqual "" expect actual

        , testCase "applies substitution from left term" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike
                            (mkAnd
                                Mock.a
                                (mkEquals Mock.testSort Mock.b (mkElemVar x'))
                            )
                        )
                        []
                        (OrPattern.fromTermLike
                            (Mock.functional10 (mkElemVar x'))
                        )
                expect =
                    [ mkAllPathClaim
                        (Pattern.withCondition Mock.a
                            (Condition.assign (inject x') Mock.b)
                        )
                        []
                        (OrPattern.fromTermLike (Mock.functional10 Mock.b))
                    ]
            actual <- runSimpl claim
            assertEqual "" expect actual

        , testCase "simplifies requires predicate" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.withCondition Mock.a
                            (makeEqualsPredicate_ Mock.c Mock.c
                                & Condition.fromPredicate
                            )
                        )
                        []
                        (OrPattern.fromTermLike Mock.b)
                expected =
                    [ mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike Mock.b)
                    ]

            actual <- runSimpl claim

            assertEqual "" expected actual

        , testCase "applies substitution from requires" $ do
            let expected =
                    [ mkAllPathClaim
                        (Pattern.withCondition Mock.a
                            (Condition.assign (inject x') Mock.b)
                        )
                        []
                        (Pattern.fromTermLike (Mock.f Mock.b)
                            & Pattern.requireDefined
                            & OrPattern.fromPattern
                        )
                    ]
            actual <-
                mkAllPathClaim
                    (Pattern.withCondition Mock.a
                        (makeEqualsPredicate_ Mock.b (mkElemVar x')
                            & Condition.fromPredicate
                        )
                    )
                    []
                    (OrPattern.fromTermLike (Mock.f $ mkElemVar x'))
                & runSimpl

            assertEqual "" expected actual

        , testCase "splits rule on disjunction in left-hand term" $ do
            let expected =
                    [ mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike Mock.c)
                    , mkAllPathClaim
                        (Pattern.fromTermLike Mock.b)
                        []
                        (OrPattern.fromTermLike Mock.c)
                    ]

            actual <-
                mkAllPathClaim
                    (Pattern.fromTermLike (mkOr Mock.a Mock.b))
                    []
                    (OrPattern.fromTermLike Mock.c)
                & runSimpl

            assertEqual "" expected actual
        ]

    , testGroup "simplifies right-hand side"
        [ testCase "simplifies right-hand term" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike
                            (mkAnd
                                Mock.b
                                (mkEquals Mock.testSort Mock.a Mock.a)
                            )
                        )
                expected =
                    [ mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike Mock.b)
                    ]

            actual <- runSimpl claim

            assertEqual "" expected actual

        , testCase "simplifies ensures predicate" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (Pattern.withCondition Mock.b
                            (makeEqualsPredicate_ Mock.c Mock.c
                                & Condition.fromPredicate
                            )
                            & OrPattern.fromPattern
                        )
                expected =
                    [ mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike Mock.b)
                    ]

            actual <- runSimpl claim

            assertEqual "" expected actual
        ]

    , testGroup "infers left-hand side is defined"
        [ testCase "left-hand side is partial" $ do
            let expected =
                    [ mkAllPathClaim
                        (Pattern.withCondition
                            (mkDefined (Mock.f Mock.b))
                            (Condition.fromPredicate
                                (makeCeilPredicate_ (Mock.f Mock.b))
                            )
                        )
                        []
                        (OrPattern.fromTermLike Mock.a)
                    ]

            actual <-
                mkAllPathClaim
                    (Pattern.fromTermLike (Mock.f Mock.b))
                    []
                    (OrPattern.fromTermLike Mock.a)
                & runSimpl

            assertEqual "" expected actual
        , testCase "left-hand side is total" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike (Mock.functional10 Mock.b))
                        []
                        (OrPattern.fromTermLike Mock.a)
                expected = [ claim ]

            actual <- runSimpl claim

            assertEqual "" expected actual
        ]

    , testGroup "infers right-hand side is defined"
        [ testCase "right-hand side is total" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike $ Mock.functional10 Mock.b)
                expected = [ claim ]
            actual <- runSimpl claim
            assertEqual "" expected actual

        , testCase "right-hand side is partial" $ do
            let claim =
                    mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (OrPattern.fromTermLike $ Mock.f Mock.b)
                expected =
                    [ mkAllPathClaim
                        (Pattern.fromTermLike Mock.a)
                        []
                        (Pattern.withCondition (Mock.f Mock.b)
                            (makeCeilPredicate_ (Mock.f Mock.b)
                                & Condition.fromPredicate
                            )
                            & OrPattern.fromPattern
                        )
                    ]
            actual <- runSimpl claim
            assertEqual "" expected actual
        ]

    , testCase "Predicate simplification removes trivial claim" $ do
        let expected = []
            requires =
                makeAndPredicate
                    (makeNotPredicate
                        (makeEqualsPredicate_ (mkElemVar x') Mock.b)
                    )
                    (makeNotPredicate
                        (makeNotPredicate
                            (makeEqualsPredicate_ (mkElemVar x') Mock.b)
                        )
                    )
        actual <-
            mkAllPathClaim
                (Pattern.withCondition Mock.b
                    (Condition.fromPredicate requires)
                )
                []
                (OrPattern.fromTermLike Mock.a)
            & runSimpl
        assertEqual "" expected actual

    ]
  where
    simplClaim
        :: forall simplifier
        .  MonadSimplify simplifier
        => AllPathClaim
        -> simplifier [AllPathClaim]
    simplClaim claim = Foldable.toList <$> simplify claim

    runSimpl :: AllPathClaim -> IO [AllPathClaim]
    runSimpl claim =
        simplClaim claim
        & runSimplifier Mock.env
        & runSMT (pure ())

    x' = Mock.x & TermLike.mapElementVariable (pure mkRuleVariable)
