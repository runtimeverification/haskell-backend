module Test.Kore.Step.Rule.Simplify
    ( test_simplifyRule
    , test_simplifyClaimRule
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Lens as Lens
import Data.Default
    ( def
    )
import Data.Generics.Product
    ( field
    )

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( extractPatterns
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
    ( TermLike
    , mkAnd
    , mkElemVar
    , mkEquals_
    , mkOr
    , termLikeSort
    )
import Kore.Log
    ( emptyLogger
    )
import Kore.Sort
    ( predicateSort
    )
import Kore.Step.Rule.Simplify
import Kore.Step.RulePattern
    ( OnePathRule (..)
    , RHS (..)
    , RulePattern (RulePattern)
    , rulePattern
    )
import qualified Kore.Step.RulePattern as Rule.DoNotUse
import Kore.Step.Simplification.Data
    ( Env (..)
    , runSimplifier
    )
import Kore.Step.Simplification.Simplify
    ( emptyConditionSimplifier
    , termLikeSimplifier
    )
import qualified Kore.Step.SMT.Declaration.All as SMT.All
import Kore.Syntax.Variable
    ( Variable
    , fromVariable
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
            , requires = p1
            , rhs = RHS
                { existentials = []
                , right = t2
                , ensures = p2
                }
            , antiLeft = Nothing
            , attributes = def
            }

instance OnePathRuleBase TermLike where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate (termLikeSort t1))
        `rewritesTo` Pair (t2, makeTruePredicate_)

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
                Pair (Mock.a,  makeTruePredicate Mock.testSort)
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
                [   Pair (Mock.f x, makeCeilPredicate Mock.testSort (Mock.f x))
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
    $ runSimplifier Mock.env $ do
        SMT.All.declare Mock.smtDeclarations
        simplifyRuleLhs rule

test_simplifyClaimRule :: [TestTree]
test_simplifyClaimRule =
    [ test "infers definedness"
        rule1
        [rule1']
    , test "includes side condition"
        rule2
        [rule2']
    ]
  where
    rule1, rule2, rule2' :: RulePattern Variable
    rule1 = rulePattern (Mock.f Mock.a) Mock.b
    rule1' = rule1 & requireDefined
    rule2 =
        rulePattern @Variable (Mock.g Mock.a) Mock.b
        & Lens.set (field @"requires") requires
    rule2' =
        rule2
        & requireDefined
        & Lens.set (field @"left") (Mock.f Mock.a)

    requires :: Predicate Variable
    requires = makeEqualsPredicate Mock.testSort Mock.a Mock.b

    requireDefined rule =
        Lens.over
            (field @"requires")
            (flip makeAndPredicate
                (makeCeilPredicate sort left)
            )
            rule
      where
        left = Lens.view (field @"left") rule
        sort = termLikeSort left

    test
        :: HasCallStack
        => TestName
        -> RulePattern Variable
        -> [RulePattern Variable]
        -> TestTree
    test name (OnePathRule -> input) (map OnePathRule -> expect) =
        -- Test simplifyClaimRule through the OnePathRule instance.
        testCase name $ do
            actual <- run $ simplifyRuleLhs input
            assertEqual "" expect (MultiAnd.extractPatterns actual)
      where
        run = SMT.runNoSMT emptyLogger . runSimplifier env
        env =
            Mock.env
                { simplifierTermLike
                , simplifierCondition = emptyConditionSimplifier
                , simplifierAxioms = mempty
                }
        simplifierTermLike = termLikeSimplifier $ \sideCondition termLike -> do
            let rule = getOnePathRule input
                left = Lens.view (field @"left") rule
                sort = termLikeSort left
                expectSideCondition =
                    makeAndPredicate requires (makeCeilPredicate sort left)
                    & Predicate.mapVariables
                        (fmap fromVariable)
                        (fmap fromVariable)
                    & Predicate.coerceSort predicateSort
                    & Condition.fromPredicate
                    & SideCondition.fromCondition
            return . OrPattern.fromTermLike
                $ if
                    (termLike == Mock.g Mock.a)
                    && (sideCondition == expectSideCondition)
                    then Mock.f Mock.a
                    else termLike
