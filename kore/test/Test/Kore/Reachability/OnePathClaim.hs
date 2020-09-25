module Test.Kore.Reachability.OnePathClaim
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
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeNotPredicate
    , makeTruePredicate
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
    ( OnePathClaim (..)
    , simplify
    )
import Kore.Rewriting.RewritingVariable
    ( mkRuleVariable
    )
import Kore.Step.ClaimPattern
    ( mkClaimPattern
    )
import Kore.Step.Simplification.Data
    ( runSimplifier
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    )
import Kore.Syntax.Variable
    ( VariableName
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Rule.Common
    ( Pair (..)
    , RuleBase
    )
import qualified Test.Kore.Step.Rule.Common as Common
import Test.SMT
    ( runSMT
    )
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testCase "already simplified" $ do
        let claim =
                mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike Mock.b)
                & OnePathClaim
            expect = [claim]
        actual <- runSimpl claim
        assertEqual "" expect actual

    , testCase "simplify left term" $ do
        let claim =
                mkClaimPattern
                    (Pattern.fromTermLike
                        (mkAnd Mock.a (mkEquals Mock.testSort Mock.a Mock.a))
                    )
                    []
                    (OrPattern.fromTermLike Mock.b)
                & OnePathClaim
            expect =
                [ mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike Mock.b)
                    & OnePathClaim
                ]
        actual <- runSimpl claim
        assertEqual "" expect actual

    , testCase "simplify right term" $ do
        let claim =
                mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike
                        (mkAnd Mock.b (mkEquals Mock.testSort Mock.a Mock.a))
                    )
                & OnePathClaim
            expected =
                [ mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike Mock.b)
                    & OnePathClaim
                ]

        actual <- runSimpl claim

        assertEqual "" expected actual

    , testCase "applies substitution from left term" $ do
        let claim =
                mkClaimPattern
                    (Pattern.fromTermLike
                        (mkAnd
                            Mock.a
                            (mkEquals Mock.testSort Mock.b (mkElemVar x'))
                        )
                    )
                    []
                    (OrPattern.fromTermLike (Mock.functional10 (mkElemVar x')))
                & OnePathClaim
            expect =
                [ mkClaimPattern
                    (Pattern.withCondition Mock.a
                        (Condition.assign (inject x') Mock.b)
                    )
                    []
                    (OrPattern.fromTermLike (Mock.functional10 Mock.b))
                    & OnePathClaim
                ]
        actual <- runSimpl claim
        assertEqual "" expect actual

    , testCase "simplifies requires predicate" $ do
        let claim =
                mkClaimPattern
                    (Pattern.withCondition Mock.a
                        (makeEqualsPredicate_ Mock.c Mock.c
                            & Condition.fromPredicate
                        )
                    )
                    []
                    (OrPattern.fromTermLike Mock.b)
                & OnePathClaim
            expected =
                [ mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike Mock.b)
                    & OnePathClaim
                ]

        actual <- runSimpl claim

        assertEqual "" expected actual

    , testCase "simplifies ensures predicate" $ do
        let claim =
                mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (Pattern.withCondition Mock.b
                        (makeEqualsPredicate_ Mock.c Mock.c
                            & Condition.fromPredicate
                        )
                        & OrPattern.fromPattern
                    )
                & OnePathClaim
            expected =
                [ mkClaimPattern
                    (Pattern.fromTermLike Mock.a)
                    []
                    (OrPattern.fromTermLike Mock.b)
                    & OnePathClaim
                ]

        actual <- runSimpl claim

        assertEqual "" expected actual

    , testCase "applies substitution from requires" $ do
        let expected =
                [ OnePathClaim $ mkClaimPattern
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
            mkClaimPattern
                (Pattern.withCondition Mock.a
                    (makeEqualsPredicate_ Mock.b (mkElemVar x')
                        & Condition.fromPredicate
                    )
                )
                []
                (OrPattern.fromTermLike (Mock.f $ mkElemVar x'))
            & OnePathClaim
            & runSimpl

        assertEqual "" expected actual

    , testCase "Splits rule" $ do
        let expected =
                [ Mock.a `rewritesToWithSort` Mock.c
                , Mock.b `rewritesToWithSort` Mock.c
                ]

        actual <- runSimpl
            (   mkOr Mock.a Mock.b
                `rewritesToWithSort`
                Mock.c
            )

        assertEqual "" expected actual
    , testCase "Case where f(x) is defined;\
               \ Case where it is not is simplified" $ do
        let expected =
                [   Pair
                        ( mkDefined (Mock.f x)
                        , makeCeilPredicate Mock.testSort (Mock.f x)
                        )
                    `rewritesToWithSort`
                    Pair (Mock.a, makeTruePredicate Mock.testSort)
                ]

        actual <- runSimpl
            (   Pair (Mock.f x, makeTruePredicate Mock.testSort)
                `rewritesToWithSort`
                Pair (Mock.a, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual
    , testCase "lhs: f(x) is always defined" $ do
        let expected =
                [ Mock.functional10 x `rewritesToWithSort` Mock.a
                ]

        actual <- runSimpl
            (   Pair (Mock.functional10 x, makeTruePredicate Mock.testSort)
                `rewritesToWithSort`
                Pair (Mock.a, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual
    , testCase "Predicate simplification removes trivial claim" $ do
        let expected = []
        actual <- runSimpl
            ( Pair
                ( Mock.b
                , makeAndPredicate
                    (makeNotPredicate
                        (makeEqualsPredicate Mock.testSort x Mock.b)
                    )
                    (makeNotPredicate
                        (makeNotPredicate
                            (makeEqualsPredicate Mock.testSort x Mock.b)
                        )
                    )
                )
              `rewritesToWithSort`
              Pair (Mock.a, makeTruePredicate Mock.testSort)
            )
        assertEqual "" expected actual

    , testCase "rhs: f(x) is always defined" $ do
        let expected =
                [ Mock.a `rewritesToWithSort` Mock.functional10 x
                ]

        actual <- runSimpl
            (   Pair (Mock.a, makeTruePredicate Mock.testSort)
                `rewritesToWithSort`
                Pair (Mock.functional10 x, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual

    , testCase "infer rhs is defined" $ do
        let expected =
                [   Pair (Mock.a, makeTruePredicate Mock.testSort)
                    `rewritesToWithSort`
                    Pair (Mock.f x, makeCeilPredicate Mock.testSort (Mock.f x))
                ]

        actual <- runSimpl
            (   Pair (Mock.a, makeTruePredicate Mock.testSort)
                `rewritesToWithSort`
                Pair (Mock.f x, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual
    ]
  where
    simplClaim
        :: forall simplifier
        .  MonadSimplify simplifier
        => OnePathClaim
        -> simplifier [OnePathClaim]
    simplClaim claim = Foldable.toList <$> simplify claim

    runSimpl :: OnePathClaim -> IO [OnePathClaim]
    runSimpl claim =
        simplClaim claim
        & runSimplifier Mock.env
        & runSMT (pure ())

    rewritesToWithSort
        :: RuleBase base OnePathClaim
        => base VariableName
        -> base VariableName
        -> OnePathClaim
    rewritesToWithSort = Common.rewritesToWithSort

    x = mkElemVar Mock.x
    x' = Mock.x & TermLike.mapElementVariable (pure mkRuleVariable)
