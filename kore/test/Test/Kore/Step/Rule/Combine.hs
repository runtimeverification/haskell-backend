module Test.Kore.Step.Rule.Combine where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Default
    ( def
    )

import Kore.Internal.TermLike
    ( TermLike
    , mkAnd
    , mkElemVar
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeMultipleAndPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Rule
    ( RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as Rule.DoNotUse
import Kore.Step.Rule.Combine
import Kore.Syntax.Variable
    ( Variable
    )

import Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Extensions

class RewriteRuleBase base where
    rewritesTo :: base Variable -> base Variable -> RewriteRule Variable

newtype Pair variable = Pair (TermLike variable, Syntax.Predicate variable)

instance RewriteRuleBase Pair where
    Pair (t1, p1) `rewritesTo` Pair (t2, p2) =
        RewriteRule RulePattern
            { left = t1
            , right = t2
            , requires = p1
            , ensures = p2
            , antiLeft = Nothing
            , attributes = def
            }

instance RewriteRuleBase TermLike where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate) `rewritesTo` Pair (t2, makeTruePredicate)

test_combineRules :: [TestTree]
test_combineRules =
    [ testCase "One rule" $
        let expected = makeTruePredicate
            actual = mergeRulesPredicate
                [ Mock.a `rewritesTo` Mock.cf ]
        in assertEqualWithExplanation "" expected actual
    , testCase "Two rules" $
        let expected = makeCeilPredicate (mkAnd Mock.cf Mock.b)
            actual = mergeRulesPredicate
                [ Mock.a `rewritesTo` Mock.cf
                , Mock.b `rewritesTo` Mock.cg
                ]
        in assertEqualWithExplanation "" expected actual
    , testCase "Three rules case" $
        let expected =
                makeAndPredicate
                    (makeCeilPredicate (mkAnd Mock.cf Mock.b))
                    (makeCeilPredicate (mkAnd Mock.cg Mock.c))

            actual = mergeRulesPredicate
                [ Mock.a `rewritesTo` Mock.cf
                , Mock.b `rewritesTo` Mock.cg
                , Mock.c `rewritesTo` Mock.ch
                ]
        in assertEqualWithExplanation "" expected actual
    , testCase "Rules with predicates" $
        let expected =
                makeMultipleAndPredicate
                    [ makeMultipleAndPredicate
                        [ makeCeilPredicate (mkAnd Mock.cf Mock.b)
                        , makeCeilPredicate (Mock.g Mock.a)
                        , makeCeilPredicate (Mock.f Mock.b)
                        ]
                    , makeMultipleAndPredicate
                        [ makeCeilPredicate (mkAnd Mock.cg Mock.c)
                        , makeCeilPredicate (Mock.g Mock.b)
                        , makeCeilPredicate (Mock.f Mock.c)
                        ]
                    ]
            actual = mergeRulesPredicate
                [   Pair (Mock.a, makeCeilPredicate (Mock.f Mock.a))
                    `rewritesTo`
                    Pair (Mock.cf, makeCeilPredicate (Mock.g Mock.a))

                ,   Pair (Mock.b, makeCeilPredicate (Mock.f Mock.b))
                    `rewritesTo`
                    Pair (Mock.cg, makeCeilPredicate (Mock.g Mock.b))

                ,   Pair (Mock.c, makeCeilPredicate (Mock.f Mock.c))
                    `rewritesTo`
                    Pair (Mock.ch, makeCeilPredicate (Mock.g Mock.c))
                ]
        in assertEqualWithExplanation "" expected actual
    , testCase "Rules with variables" $
        let expected =
                makeMultipleAndPredicate
                    [ makeCeilPredicate (mkAnd (Mock.g x) (Mock.constr11 x_0))
                    , makeCeilPredicate (Mock.g x)
                    , makeCeilPredicate (Mock.h x_0)
                    ]
            actual = mergeRulesPredicate
                [   Pair (Mock.constr10 x, makeCeilPredicate (Mock.f x))
                    `rewritesTo`
                    Pair (Mock.g x, makeCeilPredicate (Mock.g x))

                ,   Pair (Mock.constr11 x, makeCeilPredicate (Mock.h x))
                    `rewritesTo`
                    Pair (Mock.h x, makeCeilPredicate (Mock.h Mock.a))
                ]
        in assertEqualWithExplanation "" expected actual
    ]
  where
    x :: TermLike Variable
    x = mkElemVar Mock.x
    x_0 :: TermLike Variable
    x_0 = mkElemVar Mock.var_x_0
