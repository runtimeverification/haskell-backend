module Test.Kore.Rewrite (
    test_stepStrategy,
    test_executionStrategy,
) where

import qualified Control.Exception as Exception
import qualified Control.Lens as Lens
import Control.Monad.Catch (
    MonadThrow,
 )
import Data.Generics.Product
import Data.Generics.Wrapped (
    _Unwrapped,
 )
import Data.Limit (
    Limit (..),
 )
import Hedgehog (
    Gen,
 )
import qualified Hedgehog
import qualified Hedgehog.Gen
import qualified Hedgehog.Range
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeNotPredicate,
 )
import Kore.Internal.TermLike (
    TermLike,
    mkElemVar,
 )
import Kore.Rewrite hiding (
    Start,
 )
import qualified Kore.Rewrite as Step
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    RewriteRule (RewriteRule),
    mkRewritingRule,
 )
import Kore.Rewrite.RulePattern as RulePattern (
    rulePattern,
 )
import qualified Kore.Rewrite.Strategy as Strategy
import Kore.Syntax.Variable
import Prelude.Kore
import qualified Test.Kore.Internal.Pattern as Pattern
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Tasty.Hedgehog

test_stepStrategy :: [TestTree]
test_stepStrategy =
    [ testGroup "depth = 0: remains in Start" $
        let mkTest name strategy' =
                testCase name $ do
                    [actual] <-
                        runStep
                            (Limit 0)
                            Unlimited
                            strategy'
                            aPatt
                            [simpleRewrite Mock.a Mock.b]
                    assertEqual "" (Step.Start aPatt) actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "depth = 1: applies rewrite rule, transitions to Rewritten" $
        let mkTest name strategy' =
                testCase name $ do
                    [actual] <-
                        runStep
                            (Limit 1)
                            Unlimited
                            strategy'
                            aPatt
                            [simpleRewrite Mock.a Mock.b]
                    assertEqual "" (Step.Rewritten bPatt) actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "depth = 2: no more rules can apply, becomes Remaining" $
        let mkTest name strategy' =
                testCase name $ do
                    [actual] <-
                        runStep
                            (Limit 2)
                            Unlimited
                            strategy'
                            aPatt
                            [simpleRewrite Mock.a Mock.b]
                    assertEqual "" (Step.Remaining bPatt) actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "breadth = 1: fails when breadth limit is exceeded" $
        let mkTest name strategy' =
                testCase name $ do
                    actual <-
                        runStepSMT
                            Unlimited
                            (Limit 1)
                            strategy'
                            xPatt
                            [simpleRewrite Mock.a Mock.b]
                            & try
                    expectLimitExceeded actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "single rule application with remainder" $
        let mkTest name strategy' =
                testCase name $ do
                    actual <-
                        runStepSMT
                            Unlimited
                            Unlimited
                            strategy'
                            xPatt
                            [ simpleRewrite Mock.a Mock.b
                            ]
                    let rewrittenPattern =
                            Pattern.withCondition
                                Mock.b
                                (Condition.assign (inject Mock.x) Mock.a)
                        remainderPattern =
                            Pattern.fromTermAndPredicate
                                xTerm
                                ( makeNotPredicate $
                                    makeEqualsPredicate
                                        xTerm
                                        Mock.a
                                )
                    assertEqual
                        ""
                        [ Step.Remaining remainderPattern
                        , Step.Remaining rewrittenPattern
                        ]
                        actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "multiple rules, narrowing, variable renaming, remainders" $
        -- Program: c10( f( X ) )
        -- Rewrite rules:
        --   - c10( a )      => c11( g( X ) )
        --   - c11( g( b ) ) => c
        let mkTest name strategy' =
                testCase name $ do
                    actual <-
                        runStepSMT
                            Unlimited
                            Unlimited
                            strategy'
                            ( Mock.functionalConstr10 (Mock.f xTerm)
                                & Pattern.fromTermLike
                            )
                            [ simpleRewrite
                                (Mock.functionalConstr10 Mock.a)
                                (Mock.functionalConstr11 (Mock.g xTerm))
                            , simpleRewrite
                                ( Mock.functionalConstr11
                                    (Mock.g Mock.b)
                                )
                                Mock.c
                            ]
                    let -- f( X ) /\ not( a == f( X ) )
                        firstRemainderPattern =
                            Pattern.fromTermAndPredicate
                                (Mock.functionalConstr10 (Mock.f xTerm))
                                ( makeNotPredicate $
                                    makeEqualsPredicate
                                        Mock.a
                                        (Mock.f xTerm)
                                )
                        --    c11 ( g( X0 ) )
                        -- /\ a == f( X )
                        -- /\ not( ceil( g( b ) ) /\ g( b ) == g( X0 ) )
                        secondRemainderPattern =
                            Pattern.fromTermAndPredicate
                                (Mock.functionalConstr11 (Mock.g (mkElemVar Mock.var_x_0)))
                                ( makeAndPredicate
                                    ( makeEqualsPredicate
                                        Mock.a
                                        (Mock.f xTerm)
                                    )
                                    ( makeNotPredicate
                                        ( makeAndPredicate
                                            ( makeCeilPredicate
                                                (Mock.g Mock.b)
                                            )
                                            ( makeEqualsPredicate
                                                (Mock.g Mock.b)
                                                (Mock.g (mkElemVar Mock.var_x_0))
                                            )
                                        )
                                    )
                                )
                        -- c /\ ceil( g( b ) ) /\ a == f( X ) /\ g( b ) == g( X0 )
                        finalRewrittenPattern =
                            Pattern.fromTermAndPredicate
                                Mock.c
                                ( makeAndPredicate
                                    (makeCeilPredicate (Mock.g Mock.b))
                                    ( makeAndPredicate
                                        ( makeEqualsPredicate
                                            Mock.a
                                            (Mock.f xTerm)
                                        )
                                        ( makeEqualsPredicate
                                            (Mock.g Mock.b)
                                            (Mock.g (mkElemVar Mock.var_x_0))
                                        )
                                    )
                                )
                    let expected =
                            [ Step.Remaining firstRemainderPattern
                            , Step.Remaining secondRemainderPattern
                            , Step.Remaining finalRewrittenPattern
                            ]
                    Pattern.assertEquivalentPatterns' expected actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "applies rules in priority order" $
        let mkTest name strategy' =
                testCase name $ do
                    actual <-
                        runStep
                            Unlimited
                            Unlimited
                            strategy'
                            aPatt
                            [ simplePriorityRewrite Mock.a Mock.b 2
                            , simplePriorityRewrite Mock.a Mock.c 1
                            , simpleRewrite Mock.c Mock.d
                            ]
                    assertEqual
                        ""
                        [Step.Remaining dPatt]
                        actual
         in [ mkTest "strategy all" All
            , mkTest "strategy any" Any
            ]
    , testGroup "non-deterministic rules" $
        let program = aPatt
            rules =
                [ simpleRewrite Mock.a Mock.b
                , simpleRewrite Mock.a Mock.c
                ]
         in [ testCase "strategy all: considers both branches" $ do
                actual <-
                    runStep Unlimited Unlimited All program rules
                assertEqual
                    ""
                    [Step.Remaining bPatt, Step.Remaining cPatt]
                    actual
            , testCase "strategy any: picks only one branch" $ do
                actual <-
                    runStep Unlimited Unlimited Any program rules
                assertEqual
                    ""
                    [Step.Remaining bPatt]
                    actual
            ]
    ]
  where
    aPatt = Pattern.fromTermLike Mock.a
    bPatt = Pattern.fromTermLike Mock.b
    cPatt = Pattern.fromTermLike Mock.c
    dPatt = Pattern.fromTermLike Mock.d
    xPatt = Pattern.fromTermLike xTerm
    xTerm = mkElemVar Mock.x

    try ::
        Exception.Exception e =>
        e ~ Strategy.LimitExceeded Int =>
        IO a ->
        IO (Either e a)
    try = Exception.try
    expectLimitExceeded result =
        case result of
            Left (Strategy.LimitExceeded _) ->
                return ()
            Right _ ->
                assertFailure "Expected exception LimitExceeded"

test_executionStrategy :: [TestTree]
test_executionStrategy =
    [ testProperty "every step contains Rewrite" $
        Hedgehog.property $ do
            strategies <- Hedgehog.forAll genStrategies
            for_ strategies $ \strategy -> do
                Hedgehog.annotateShow strategy
                Hedgehog.assert (hasRewrite strategy)
    , testProperty "Simplify is the last sub-step" $
        Hedgehog.property $ do
            strategies <- Hedgehog.forAll genStrategies
            let strategy = last strategies
            Hedgehog.annotateShow strategy
            Hedgehog.assert (isLastSimplify strategy)
    ]
  where
    genStrategies :: Gen [Strategy Prim]
    genStrategies = do
        let range = Hedgehog.Gen.integral (Hedgehog.Range.linear 1 16)
        depthLimit <- Limit <$> range
        pure (limitedExecutionStrategy depthLimit)

    hasRewrite :: Strategy Prim -> Bool
    hasRewrite = \case
        Strategy.Seq s1 s2 -> hasRewrite s1 || hasRewrite s2
        Strategy.And s1 s2 -> hasRewrite s1 || hasRewrite s2
        Strategy.Or s1 s2 -> hasRewrite s1 || hasRewrite s2
        Strategy.Apply p -> p == Rewrite
        Strategy.Stuck -> False
        Strategy.Continue -> False

    isLastSimplify :: Strategy Prim -> Bool
    isLastSimplify = \case
        Strategy.Seq s Strategy.Continue -> isLastSimplify s
        Strategy.Seq s Strategy.Stuck -> isLastSimplify s
        Strategy.Seq _ s -> isLastSimplify s
        Strategy.And s1 s2 -> isLastSimplify s1 && isLastSimplify s2
        Strategy.Or s1 s2 -> isLastSimplify s1 && isLastSimplify s2
        Strategy.Apply p -> p == Simplify
        Strategy.Stuck -> False
        Strategy.Continue -> False

simpleRewrite ::
    TermLike VariableName ->
    TermLike VariableName ->
    RewriteRule RewritingVariableName
simpleRewrite left right =
    mkRewritingRule $
        RewriteRule $
            rulePattern left right

simplePriorityRewrite ::
    TermLike VariableName ->
    TermLike VariableName ->
    Integer ->
    RewriteRule RewritingVariableName
simplePriorityRewrite left right priority =
    Lens.set
        ( _Unwrapped
            . field @"attributes"
            . field @"priority"
        )
        (Attribute.Priority (Just priority))
        (simpleRewrite left right)

runStep ::
    -- | depth limit
    Limit Natural ->
    -- | breadth limit
    Limit Natural ->
    -- | execution mode
    ExecutionMode ->
    -- |left-hand-side of unification
    Pattern VariableName ->
    [RewriteRule RewritingVariableName] ->
    IO [ProgramState (Pattern VariableName)]
runStep = runStepWorker runSimplifier

runStepSMT ::
    -- | depth limit
    Limit Natural ->
    -- | breadth limit
    Limit Natural ->
    -- | execution mode
    ExecutionMode ->
    -- |left-hand-side of unification
    Pattern VariableName ->
    [RewriteRule RewritingVariableName] ->
    IO [ProgramState (Pattern VariableName)]
runStepSMT = runStepWorker runSimplifierSMT

runStepWorker ::
    result
        ~ Strategy.ExecutionGraph
            (ProgramState (Pattern RewritingVariableName))
            (RewriteRule RewritingVariableName) =>
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    (Env simplifier -> simplifier result -> IO result) ->
    -- | depth limit
    Limit Natural ->
    -- | breadth limit
    Limit Natural ->
    -- | execution mode
    ExecutionMode ->
    -- |left-hand-side of unification
    Pattern VariableName ->
    [RewriteRule RewritingVariableName] ->
    IO [ProgramState (Pattern VariableName)]
runStepWorker
    simplifier
    depthLimit
    breadthLimit
    execStrategy
    configuration
    rules =
        do
            result <-
                simplifier Mock.env $
                    runStrategy
                        breadthLimit
                        (transitionRule groupedRewrites execStrategy)
                        limitedDepth
                        (Step.Start $ mkRewritingPattern configuration)
            let finalResult =
                    fmap getRewritingPattern
                        <$> pickFinal result
            return finalResult
      where
        groupedRewrites = groupRewritesByPriority rules
        limitedDepth = limitedExecutionStrategy depthLimit
