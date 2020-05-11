module Test.Kore.Step.Rule.Simplify
    ( test_simplifyRule
    , test_simplifyClaimRule
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Lens as Lens
import qualified Data.Bifunctor as Bifunctor
import Data.Default
    ( def
    )
import qualified Data.Foldable as Foldable
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
    , makeNotPredicate
    , makeTruePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , mkAnd
    , mkElemVar
    , mkEquals
    , mkOr
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
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

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SMT
    ( runNoSMT
    )
import Test.Tasty.HUnit.Ext

class OnePathRuleBase base where
    rewritesTo :: base Variable -> base Variable -> OnePathRule

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
        `rewritesTo` Pair (t2, makeTruePredicate (termLikeSort t2))

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
            (   mkAnd Mock.a (mkEquals Mock.testSort Mock.a Mock.a)
                `rewritesTo`
                Mock.cf
            )

        assertEqual "" expected actual

    , testCase "Does not simplify rhs term" $ do
        let rule =
                Mock.a
                `rewritesTo`
                mkAnd Mock.cf (mkEquals Mock.testSort Mock.a Mock.a)
            expected = [rule]

        actual <- runSimplifyRule rule

        assertEqual "" expected actual

    , testCase "Substitution in lhs term" $ do
        let expected = [Mock.a `rewritesTo` Mock.f Mock.b]

        actual <- runSimplifyRule
            (   mkAnd Mock.a (mkEquals Mock.testSort Mock.b x)
                `rewritesTo` Mock.f x
            )

        assertEqual "" expected actual

    , testCase "Simplifies requires predicate" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runSimplifyRule
            (   Pair (Mock.a,  makeEqualsPredicate Mock.testSort Mock.b Mock.b)
                `rewritesTo`
                Pair (Mock.cf, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual

    , testCase "Does not simplify ensures predicate" $ do
        let rule =
                Pair (Mock.a,  makeTruePredicate Mock.testSort)
                `rewritesTo`
                Pair (Mock.cf, makeEqualsPredicate Mock.testSort Mock.b Mock.b)
            expected = [rule]

        actual <- runSimplifyRule rule

        assertEqual "" expected actual

    , testCase "Substitution in requires predicate" $ do
        let expected = [Mock.a `rewritesTo` Mock.f Mock.b]

        actual <- runSimplifyRule
            (   Pair (Mock.a,  makeEqualsPredicate Mock.testSort Mock.b x)
                `rewritesTo`
                Pair (Mock.f x, makeTruePredicate Mock.testSort)
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
                    Pair (Mock.a, makeTruePredicate Mock.testSort)
                ]

        actual <- runSimplifyRule
            (   Pair (Mock.f x, makeTruePredicate Mock.testSort)
                `rewritesTo`
                Pair (Mock.a, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual
    , testCase "f(x) is always defined" $ do
        let expected =
                [ Mock.functional10 x `rewritesTo` Mock.a
                ]

        actual <- runSimplifyRule
            (   Pair (Mock.functional10 x, makeTruePredicate Mock.testSort)
                `rewritesTo`
                Pair (Mock.a, makeTruePredicate Mock.testSort)
            )

        assertEqual "" expected actual
    , testCase "Predicate simplification removes trivial claim" $ do
        let expected = []
        actual <- runSimplifyRule
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
              `rewritesTo`
              Pair (Mock.a, makeTruePredicate Mock.testSort)
            )
        assertEqual "" expected actual
    ]
  where
    x = mkElemVar Mock.x

runSimplifyRule
    :: OnePathRule
    -> IO [OnePathRule]
runSimplifyRule rule =
    fmap MultiAnd.extractPatterns
    $ runNoSMT
    $ runSimplifier Mock.env $ do
        SMT.All.declare Mock.smtDeclarations
        simplifyRuleLhs rule

test_simplifyClaimRule :: [TestTree]
test_simplifyClaimRule =
    [ test "infers definedness" []
        rule1
        [rule1']
    , test "includes side condition" [(Mock.g Mock.a, Mock.f Mock.a)]
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
        -> [(TermLike Variable, TermLike Variable)]  -- ^ replacements
        -> RulePattern Variable
        -> [RulePattern Variable]
        -> TestTree
    test name replacements (OnePathRule -> input) (map OnePathRule -> expect) =
        -- Test simplifyClaimRule through the OnePathRule instance.
        testCase name $ do
            actual <- run $ simplifyRuleLhs input
            assertEqual "" expect (MultiAnd.extractPatterns actual)
      where
        run = runNoSMT . runSimplifier env
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
                    & liftPredicate
                    & Predicate.coerceSort predicateSort
                    & Condition.fromPredicate
                    & SideCondition.fromCondition
                satisfied = sideCondition == expectSideCondition
            return
                . OrPattern.fromTermLike
                . (if satisfied then applyReplacements else id)
                $ termLike

        applyReplacements
            :: InternalVariable variable
            => TermLike variable
            -> TermLike variable
        applyReplacements zero =
            Foldable.foldl' applyReplacement zero
            $ map liftReplacement replacements

        applyReplacement orig (ini, fin)
          | orig == ini = fin
          | otherwise   = orig

        liftPredicate
            :: InternalVariable variable
            => Predicate Variable
            -> Predicate variable
        liftPredicate =
            Predicate.mapVariables (fmap fromVariable) (fmap fromVariable)

        liftTermLike
            :: InternalVariable variable
            => TermLike Variable
            -> TermLike variable
        liftTermLike =
            TermLike.mapVariables (fmap fromVariable) (fmap fromVariable)

        liftReplacement
            :: InternalVariable variable
            => (TermLike Variable, TermLike Variable)
            -> (TermLike variable, TermLike variable)
        liftReplacement = Bifunctor.bimap liftTermLike liftTermLike
