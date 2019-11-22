module Test.Kore.Step.Rule.Simplify
    ( test_simplifyRule
    ) where

import Test.Tasty

import Data.Default
    ( def
    )

import qualified Kore.Internal.MultiAnd as MultiAnd
    ( extractPatterns
    )
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate_
    , makeNotPredicate
    , makeTruePredicate_
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
    ( TermLike
    , mkAnd
    , mkElemVar
    , mkEquals_
    , mkOr
    )
import Kore.Logger.Output
    ( emptyLogger
    )
import Kore.Step.Rule
    ( OnePathRule (OnePathRule)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as Rule.DoNotUse
import Kore.Step.Rule.Simplify
import Kore.Step.Simplification.Data
    ( runSimplifier
    )
import Kore.Syntax.Variable
    ( Variable
    )
import qualified SMT

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

class OnePathRuleBase base where
    rewritesTo :: base Variable -> base Variable -> OnePathRule Variable

newtype Pair variable = Pair (TermLike variable, Predicate variable)

instance OnePathRuleBase Pair where
    Pair (t1, p1) `rewritesTo` Pair (t2, p2) =
        OnePathRule RulePattern
            { left = t1
            , right = t2
            , requires = p1
            , ensures = p2
            , antiLeft = Nothing
            , attributes = def
            }

instance OnePathRuleBase TermLike where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate_) `rewritesTo` Pair (t2, makeTruePredicate_)

test_simplifyRule :: [TestTree]
test_simplifyRule =
    [ testCase "No simplification needed" $ do
        let rule = Mock.a `rewritesTo` Mock.cf
            expected = [rule]

        actual <- runSimplifyRule rule

        assertEqual "" expected actual

    , testCase "Simplify lhs term" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runSimplifyRule
            (   mkAnd Mock.a (mkEquals_ Mock.a Mock.a)
                `rewritesTo`
                Mock.cf
            )

        assertEqual "" expected actual

    , testCase "Does not simplify rhs term" $ do
        let rule =
                Mock.a
                `rewritesTo`
                mkAnd Mock.cf (mkEquals_ Mock.a Mock.a)
            expected = [rule]

        actual <- runSimplifyRule rule

        assertEqual "" expected actual

    , testCase "Substitution in lhs term" $ do
        let expected = [Mock.a `rewritesTo` Mock.f Mock.b]

        actual <- runSimplifyRule
            (   mkAnd Mock.a (mkEquals_ Mock.b x)
                `rewritesTo` Mock.f x
            )

        assertEqual "" expected actual

    , testCase "Simplifies requires predicate" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runSimplifyRule
            (   Pair (Mock.a,  makeEqualsPredicate_ Mock.b Mock.b)
                `rewritesTo`
                Pair (Mock.cf, makeTruePredicate_)
            )

        assertEqual "" expected actual

    , testCase "Does not simplify ensures predicate" $ do
        let rule =
                Pair (Mock.a,  makeTruePredicate_)
                `rewritesTo`
                Pair (Mock.cf, makeEqualsPredicate_ Mock.b Mock.b)
            expected = [rule]

        actual <- runSimplifyRule rule

        assertEqual "" expected actual

    , testCase "Substitution in requires predicate" $ do
        let expected = [Mock.a `rewritesTo` Mock.f Mock.b]

        actual <- runSimplifyRule
            (   Pair (Mock.a,  makeEqualsPredicate_ Mock.b x)
                `rewritesTo`
                Pair (Mock.f x, makeTruePredicate_)
            )

        assertEqual "" expected actual

    , testCase "Splits rule" $ do
        let expected =
                [ Mock.a `rewritesTo` Mock.cf
                , Mock.b `rewritesTo` Mock.cf
                ]

        actual <- runSimplifyRule
            (   mkOr Mock.a Mock.b
                `rewritesTo`
                Mock.cf
            )

        assertEqual "" expected actual
    , testCase "Case where f(x) is defined;\
               \ Case where it is not is simplified" $ do
        let expected =
                [   Pair (Mock.f x, makeCeilPredicate_ (Mock.f x))
                    `rewritesTo`
                    Pair (Mock.a, makeTruePredicate_)
                ]

        actual <- runSimplifyRule
            (   Pair (Mock.f x, makeTruePredicate_)
                `rewritesTo`
                Pair (Mock.a, makeTruePredicate_)
            )

        assertEqual "" expected actual
    , testCase "f(x) is always defined" $ do
        let expected =
                [ Mock.functional10 x `rewritesTo` Mock.a
                ]

        actual <- runSimplifyRule
            (   Pair (Mock.functional10 x, makeTruePredicate_)
                `rewritesTo`
                Pair (Mock.a, makeTruePredicate_)
            )

        assertEqual "" expected actual
    , testCase "Predicate simplification removes trivial claim" $ do
        let expected = []
        actual <- runSimplifyRule
            ( Pair
                ( Mock.b
                , makeAndPredicate
                    (makeNotPredicate
                        (makeEqualsPredicate_ x Mock.b)
                    )
                    (makeNotPredicate
                        (makeNotPredicate
                            (makeEqualsPredicate_ x Mock.b)
                        )
                    )
                )
              `rewritesTo`
              Pair (Mock.a, makeTruePredicate_)
            )
        assertEqual "" expected actual
    ]
  where
    x = mkElemVar Mock.x

runSimplifyRule
    :: OnePathRule Variable
    -> IO [OnePathRule Variable]
runSimplifyRule rule =
    fmap MultiAnd.extractPatterns
    $ SMT.runSMT SMT.defaultConfig emptyLogger
    $ runSimplifier Mock.env
    $ simplifyRuleLhs rule
