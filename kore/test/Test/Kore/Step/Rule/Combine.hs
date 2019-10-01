module Test.Kore.Step.Rule.Combine where

import Test.Tasty

import Data.Default
    ( def
    )
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )

import Kore.Internal.TermLike
    ( TermLike
    , mkAnd
    , mkElemVar
    )
import Kore.Logger.Output
    ( emptyLogger
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
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
import Kore.Step.Simplification.Data
    ( runSimplifier
    )
import Kore.Syntax.Variable
    ( Variable
    )
import qualified SMT

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

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

test_combineRulesPredicate :: [TestTree]
test_combineRulesPredicate =
    [ testCase "One rule" $
        let expected = makeTruePredicate
            actual = mergeRulesPredicate
                [ Mock.a `rewritesTo` Mock.cf ]
        in assertEqual "" expected actual
    , testCase "Two rules" $
        let expected = makeCeilPredicate (mkAnd Mock.cf Mock.b)
            actual = mergeRulesPredicate
                [ Mock.a `rewritesTo` Mock.cf
                , Mock.b `rewritesTo` Mock.cg
                ]
        in assertEqual "" expected actual
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
        in assertEqual "" expected actual
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
        in assertEqual "" expected actual
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
        in assertEqual "" expected actual
    ]
  where
    x :: TermLike Variable
    x = mkElemVar Mock.x
    x_0 :: TermLike Variable
    x_0 = mkElemVar Mock.var_x_0

test_combineRules :: [TestTree]
test_combineRules =
    [ testCase "One rule" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runMergeRules [ Mock.a `rewritesTo` Mock.cf ]

        assertEqual "" expected actual
    , testCase "Two rules" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runMergeRules
            [ Mock.a `rewritesTo` Mock.b
            , Mock.b `rewritesTo` Mock.cf
            ]

        assertEqual "" expected actual
    , testCase "Predicate simplification" $ do
        let expected =
                [   Pair
                        ( Mock.a
                        , makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeEqualsPredicate Mock.cf Mock.b)
                        )
                    `rewritesTo` Pair (Mock.cg, makeTruePredicate)
                ]

        actual <- runMergeRules
            [ Mock.a `rewritesTo` Mock.functionalConstr10 Mock.cf
            , Mock.functionalConstr10 Mock.b `rewritesTo` Mock.cg
            ]

        assertEqual "" expected actual
    , testCase "Substitution" $ do
        let expected =
                [   Mock.functionalConstr10 (Mock.functionalConstr11 y)
                    `rewritesTo` y
                ]

        actual <- runMergeRules
            [ Mock.functionalConstr10 x `rewritesTo` x
            , Mock.functionalConstr11 y `rewritesTo` y
            ]

        assertEqual "" expected actual
    , testCase "Substitution in predicates" $ do
        let expected =
                [   Pair
                        ( Mock.functionalConstr10 (Mock.functionalConstr11 y)
                        , makeAndPredicate
                            (makeEqualsPredicate
                                (Mock.f (Mock.functionalConstr11 y))
                                (Mock.g (Mock.functionalConstr11 y))
                            )
                            (makeEqualsPredicate
                                (Mock.g (Mock.functionalConstr11 y))
                                (Mock.h (Mock.functionalConstr11 y))
                            )
                        )
                    `rewritesTo` Pair (y, makeTruePredicate)
                ]

        actual <- runMergeRules
            [   Pair
                    ( Mock.functionalConstr10 x
                    , makeEqualsPredicate (Mock.f x) (Mock.g x)
                    )
                `rewritesTo`
                Pair (x, makeEqualsPredicate (Mock.g x) (Mock.h x))
            , Mock.functionalConstr11 y `rewritesTo` y
            ]

        assertEqual "" expected actual
    , testCase "Renames variables" $ do
        let expected =
                [   Mock.functionalConstr10 (Mock.functionalConstr11 x0)
                    `rewritesTo` x0
                ]

        actual <- runMergeRules
            [ Mock.functionalConstr10 x `rewritesTo` x
            , Mock.functionalConstr11 x `rewritesTo` x
            ]

        assertEqual "" expected actual
    ]
  where
    x = mkElemVar Mock.x
    x0 = mkElemVar Mock.var_x_0
    y = mkElemVar Mock.y

runMergeRules
    :: [RewriteRule Variable]
    -> IO [RewriteRule Variable]
runMergeRules (rule : rules) =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ runSimplifier Mock.env
    $ mergeRules (rule :| rules)
runMergeRules [] = error "Unexpected empty list of rules."
