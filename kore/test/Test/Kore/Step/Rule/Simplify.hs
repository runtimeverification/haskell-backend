module Test.Kore.Step.Rule.Simplify where

import Test.Tasty

import Data.Default
    ( def
    )

import qualified Kore.Internal.MultiAnd as MultiAnd
    ( extractPatterns
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
import Kore.Predicate.Predicate
    ( makeEqualsPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Rule
    ( OnePathRule (OnePathRule)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as Rule.DoNotUse
import Kore.Step.Rule.Simplify
    ( simplifyOnePathRuleLhs
    )
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

newtype Pair variable = Pair (TermLike variable, Syntax.Predicate variable)

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
        Pair (t1, makeTruePredicate) `rewritesTo` Pair (t2, makeTruePredicate)

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
            (   Pair (Mock.a,  makeEqualsPredicate Mock.b Mock.b)
                `rewritesTo`
                Pair (Mock.cf, makeTruePredicate)
            )

        assertEqual "" expected actual

    , testCase "Does not simplify ensures predicate" $ do
        let rule =
                Pair (Mock.a,  makeTruePredicate)
                `rewritesTo`
                Pair (Mock.cf, makeEqualsPredicate Mock.b Mock.b)
            expected = [rule]

        actual <- runSimplifyRule rule

        assertEqual "" expected actual

    , testCase "Substitution in requires predicate" $ do
        let expected = [Mock.a `rewritesTo` Mock.f Mock.b]

        actual <- runSimplifyRule
            (   Pair (Mock.a,  makeEqualsPredicate Mock.b x)
                `rewritesTo`
                Pair (Mock.f x, makeTruePredicate)
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
    $ simplifyOnePathRuleLhs rule
