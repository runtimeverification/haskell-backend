module Test.Kore.Rewrite.Rule.Combine (
    test_combineRulesPredicate,
    test_combineRules,
    test_combineRulesGrouped,
) where

import Data.Default (
    def,
 )
import Data.Text (
    Text,
 )
import Kore.Internal.ApplicationSorts (
    applicationSorts,
 )
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeMultipleAndPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.TermLike (
    Alias (Alias),
    TermLike,
    mkAnd,
    mkApplyAlias,
    mkBottom_,
    mkElemVar,
    mkEquals_,
    mkOr,
 )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse
import Kore.Rewrite.AntiLeft (
    AntiLeft,
    mapVariables,
 )
import qualified Kore.Rewrite.AntiLeft as AntiLeft (
    parse,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Rewrite.Rule.Combine
import Kore.Rewrite.RulePattern (
    RHS (..),
    RewriteRule (RewriteRule),
    RulePattern (RulePattern),
 )
import qualified Kore.Rewrite.RulePattern as RulePattern (
    RulePattern (..),
 )
import Kore.Syntax.Variable
import Kore.Unparser (
    unparseToString,
 )
import Prelude.Kore
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify (
    runSimplifier,
    runSimplifierSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

class RewriteRuleBase base where
    rewritesTo ::
        base RewritingVariableName ->
        base RewritingVariableName ->
        RewriteRule RewritingVariableName

newtype Pair variable = Pair (TermLike variable, Predicate variable)

instance RewriteRuleBase Pair where
    Pair (t1, p1) `rewritesTo` Pair (t2, p2) =
        RewriteRule
            RulePattern
                { left = t1
                , requires = p1
                , rhs =
                    RHS
                        { existentials = []
                        , right = t2
                        , ensures = p2
                        }
                , antiLeft = Nothing
                , attributes = def
                }

instance RewriteRuleBase TermLike where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate) `rewritesTo` Pair (t2, makeTruePredicate)

withAntiLeft ::
    RewriteRule RewritingVariableName ->
    AntiLeft RewritingVariableName ->
    RewriteRule RewritingVariableName
withAntiLeft (RewriteRule rule) antiLeft =
    RewriteRule rule{RulePattern.antiLeft = Just antiLeft}

parseAntiLeft ::
    TermLike VariableName ->
    IO (AntiLeft VariableName)
parseAntiLeft term =
    case AntiLeft.parse term of
        Nothing ->
            assertFailure
                ("Cannot interpret " ++ unparseToString term ++ " as antileft.")
        Just antiLeft -> return antiLeft

test_combineRulesPredicate :: [TestTree]
test_combineRulesPredicate =
    [ testCase "One rule" $
        let expected = makeTruePredicate
            actual =
                mergeRulesPredicate
                    [Mock.a `rewritesTo` Mock.cf]
         in assertEqual "" expected actual
    , testCase "Two rules" $
        let expected = makeCeilPredicate (mkAnd Mock.cf Mock.b)
            actual =
                mergeRulesPredicate
                    [ Mock.a `rewritesTo` Mock.cf
                    , Mock.b `rewritesTo` Mock.cg
                    ]
         in assertEqual "" expected actual
    , testCase "Three rules case" $
        let expected =
                makeAndPredicate
                    (makeCeilPredicate (mkAnd Mock.cf Mock.b))
                    (makeCeilPredicate (mkAnd Mock.cg Mock.c))

            actual =
                mergeRulesPredicate
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
            actual =
                mergeRulesPredicate
                    [ Pair (Mock.a, makeCeilPredicate (Mock.f Mock.a))
                        `rewritesTo` Pair (Mock.cf, makeCeilPredicate (Mock.g Mock.a))
                    , Pair (Mock.b, makeCeilPredicate (Mock.f Mock.b))
                        `rewritesTo` Pair (Mock.cg, makeCeilPredicate (Mock.g Mock.b))
                    , Pair (Mock.c, makeCeilPredicate (Mock.f Mock.c))
                        `rewritesTo` Pair (Mock.ch, makeCeilPredicate (Mock.g Mock.c))
                    ]
         in assertEqual "" expected actual
    , testCase "Rules with variables" $
        let expected =
                makeMultipleAndPredicate
                    [ makeCeilPredicate (mkAnd (Mock.g x) (Mock.constr11 x_0))
                    , makeCeilPredicate (Mock.g x)
                    , makeCeilPredicate (Mock.h x_0)
                    ]
            actual =
                mergeRulesPredicate
                    [ Pair (Mock.constr10 x, makeCeilPredicate (Mock.f x))
                        `rewritesTo` Pair (Mock.g x, makeCeilPredicate (Mock.g x))
                    , Pair (Mock.constr11 x, makeCeilPredicate (Mock.h x))
                        `rewritesTo` Pair (Mock.h x, makeCeilPredicate (Mock.h Mock.a))
                    ]
         in assertEqual "" expected actual
    , testCase "Three rules case" $
        let expected =
                makeMultipleAndPredicate
                    [ makeCeilPredicate
                        (mkAnd Mock.a (mkElemVar Mock.var_xConfig_0))
                    , makeCeilPredicate
                        (mkAnd Mock.b (mkElemVar Mock.var_xConfig_1))
                    ]

            actual =
                mergeRulesPredicate
                    [ mkElemVar Mock.xConfig `rewritesTo` Mock.a
                    , mkElemVar Mock.xConfig `rewritesTo` Mock.b
                    , mkElemVar Mock.xConfig `rewritesTo` Mock.c
                    ]
         in assertEqual "" expected actual
    , testCase "Anti Left" $ do
        antiLeft <-
            parseAntiLeft
                ( applyAlias
                    "A"
                    ( mkOr
                        ( applyAlias
                            "B"
                            (mkAnd (mkEquals_ Mock.cf Mock.cg) Mock.ch)
                        )
                        mkBottom_
                    )
                )
        let expected =
                makeMultipleAndPredicate
                    [ makeCeilPredicate
                        (mkAnd Mock.a (mkElemVar Mock.var_xConfig_0))
                    , makeNotPredicate
                        ( makeAndPredicate
                            (makeEqualsPredicate Mock.cf Mock.cg)
                            (makeCeilPredicate (mkAnd Mock.a Mock.ch))
                        )
                    , makeCeilPredicate
                        (mkAnd Mock.b (mkElemVar Mock.var_xConfig_1))
                    ]

            actual =
                mergeRulesPredicate
                    [ mkElemVar Mock.xConfig `rewritesTo` Mock.a
                    , mkElemVar Mock.xConfig `rewritesTo` Mock.b
                        `withAntiLeft` mapVariables (pure mkConfigVariable) antiLeft
                    , mkElemVar Mock.xConfig `rewritesTo` Mock.c
                    ]
        assertEqual "" expected actual
    ]
  where
    x :: TermLike RewritingVariableName
    x = mkElemVar Mock.xConfig
    x_0 :: TermLike RewritingVariableName
    x_0 = mkElemVar Mock.var_xConfig_0

test_combineRules :: [TestTree]
test_combineRules =
    [ testCase "One rule" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runMergeRules [Mock.a `rewritesTo` Mock.cf]

        assertEqual "" expected actual
    , testCase "Two rules" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <-
            runMergeRules
                [ Mock.a `rewritesTo` Mock.b
                , Mock.b `rewritesTo` Mock.cf
                ]

        assertEqual "" expected actual
    , testCase "Predicate simplification" $ do
        let expected =
                [ Pair
                    ( Mock.a
                    , makeEqualsPredicate Mock.b Mock.cf
                    )
                    `rewritesTo` Pair (Mock.cg, makeTruePredicate)
                ]

        actual <-
            runMergeRulesSMT
                [ Mock.a `rewritesTo` Mock.functionalConstr10 Mock.cf
                , Mock.functionalConstr10 Mock.b `rewritesTo` Mock.cg
                ]

        assertEqual "" expected actual
    , testCase "Substitution" $ do
        let expected =
                [ Mock.functionalConstr10 (Mock.functionalConstr11 y)
                    `rewritesTo` y
                ]

        actual <-
            runMergeRules
                [ Mock.functionalConstr10 x `rewritesTo` x
                , Mock.functionalConstr11 y `rewritesTo` y
                ]

        assertEqual "" expected actual
    , testCase "Substitution in predicates" $ do
        let expected =
                [ Pair
                    ( Mock.functionalConstr10 (Mock.functionalConstr11 y)
                    , makeAndPredicate
                        ( makeEqualsPredicate
                            (Mock.f (Mock.functionalConstr11 y))
                            (Mock.g (Mock.functionalConstr11 y))
                        )
                        ( makeEqualsPredicate
                            (Mock.g (Mock.functionalConstr11 y))
                            (Mock.h (Mock.functionalConstr11 y))
                        )
                    )
                    `rewritesTo` Pair (y, makeTruePredicate)
                ]

        actual <-
            runMergeRulesSMT
                [ Pair
                    ( Mock.functionalConstr10 x
                    , makeEqualsPredicate (Mock.f x) (Mock.g x)
                    )
                    `rewritesTo` Pair (x, makeEqualsPredicate (Mock.g x) (Mock.h x))
                , Mock.functionalConstr11 y `rewritesTo` y
                ]

        assertEqual "" expected actual
    , testCase "renameRulesVariables" $ do
        let original =
                [ Mock.functionalConstr10 x `rewritesTo` x
                , Mock.functionalConstr11 x `rewritesTo` x
                ]
            expected =
                [ Mock.functionalConstr10 x `rewritesTo` x
                , Mock.functionalConstr11 x0 `rewritesTo` x0
                ]
            actual = renameRulesVariables original
        assertEqual "" expected actual
    , testCase "Renames variables" $ do
        let expected =
                [ Mock.functionalConstr10 (Mock.functionalConstr11 x0)
                    `rewritesTo` x0
                ]

        actual <-
            runMergeRules
                [ Mock.functionalConstr10 x `rewritesTo` x
                , Mock.functionalConstr11 x `rewritesTo` x
                ]

        assertEqual "" expected actual
    ]
  where
    x = mkElemVar Mock.xConfig
    x0 = mkElemVar Mock.var_xConfig_0
    y = mkElemVar Mock.yConfig

test_combineRulesGrouped :: [TestTree]
test_combineRulesGrouped =
    [ testCase "One rule" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <- runMergeRulesGrouped [Mock.a `rewritesTo` Mock.cf]

        assertEqual "" expected actual
    , testCase "Two rules" $ do
        let expected = [Mock.a `rewritesTo` Mock.cf]

        actual <-
            runMergeRules
                [ Mock.a `rewritesTo` Mock.b
                , Mock.b `rewritesTo` Mock.cf
                ]

        assertEqual "" expected actual
    , testCase "Two rules" $ do
        let expected =
                [ Mock.functionalConstr10
                    (Mock.functionalConstr11 (Mock.functionalConstr12 z))
                    `rewritesTo` z
                ]

        actual <-
            runMergeRules
                [ Mock.functionalConstr10 x `rewritesTo` x
                , Mock.functionalConstr11 y `rewritesTo` y
                , Mock.functionalConstr12 z `rewritesTo` z
                ]

        assertEqual "" expected actual
    ]
  where
    x = mkElemVar Mock.xConfig
    y = mkElemVar Mock.yConfig
    z = mkElemVar Mock.zConfig

applyAlias :: Text -> TermLike VariableName -> TermLike VariableName
applyAlias name aliasRight =
    mkApplyAlias
        Alias
            { aliasConstructor = testId name
            , aliasParams = []
            , aliasSorts = applicationSorts [] Mock.testSort
            , aliasLeft = []
            , aliasRight
            }
        []

runMergeRules ::
    [RewriteRule RewritingVariableName] ->
    IO [RewriteRule RewritingVariableName]
runMergeRules (rule : rules) =
    runSimplifier Mock.env $
        mergeRules (rule :| rules)
runMergeRules [] = error "Unexpected empty list of rules."

runMergeRulesSMT ::
    [RewriteRule RewritingVariableName] ->
    IO [RewriteRule RewritingVariableName]
runMergeRulesSMT (rule : rules) =
    runSimplifierSMT Mock.env $
        mergeRules (rule :| rules)
runMergeRulesSMT [] = error "Unexpected empty list of rules."

runMergeRulesGrouped ::
    [RewriteRule RewritingVariableName] ->
    IO [RewriteRule RewritingVariableName]
runMergeRulesGrouped (rule : rules) =
    runSimplifier Mock.env $
        mergeRulesConsecutiveBatches 2 (rule :| rules)
runMergeRulesGrouped [] = error "Unexpected empty list of rules."
