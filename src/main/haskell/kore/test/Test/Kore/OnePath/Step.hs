module Test.Kore.OnePath.Step
    ( test_onePathStrategy
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import           Data.List
                 ( nub, sort )
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Reflection
                 ( give )
import           Numeric.Natural
                 ( Natural )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Common
                 ( Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import           Kore.OnePath.Step
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeNotPredicate,
                 makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.BaseStep
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..), fromPurePattern )
import           Kore.Step.Pattern
                 ( CommonStepPattern )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Step.StepperAttributes
import           Kore.Step.Strategy
                 ( ExecutionGraph, Strategy, pickFinal, runStrategy )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_onePathStrategy :: [TestTree]
test_onePathStrategy = give symbolOrAliasSorts
    [ testCase "Runs zero steps" $ do
        -- Target: a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: a
        [ actual ] <- runOnePathSteps
            metadataTools
            (Limit 0)
            (ExpandedPattern.fromPurePattern Mock.a)
            Mock.a
            [simpleRewrite Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        assertEqualWithExplanation ""
            (RewritePattern $ ExpandedPattern.fromPurePattern Mock.a)
            actual
    , testCase "Axiom priority, first step" $ do
        -- Target: a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: bottom, since a->bottom
        [ _actual ] <- runOnePathSteps
            metadataTools
            (Limit 1)
            (ExpandedPattern.fromPurePattern Mock.a)
            Mock.a
            [simpleRewrite Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        assertEqualWithExplanation ""
            Bottom
            _actual

        -- Target: d
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: c, since coinductive axioms are applied only at the second
        -- step
        [ _actual ] <- runOnePathSteps
            metadataTools
            (Limit 1)
            (ExpandedPattern.fromPurePattern Mock.a)
            Mock.d
            [simpleRewrite Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        assertEqualWithExplanation ""
            (RewritePattern $ ExpandedPattern.fromPurePattern Mock.c)
            _actual
    , testCase "Axiom priority, second step" $ do
        -- Target: b
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: bottom, since a->b = target
        [ _actual ] <- runOnePathSteps
            metadataTools
            (Limit 2)
            (ExpandedPattern.fromPurePattern Mock.a)
            Mock.b
            [simpleRewrite Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            Bottom
            _actual

        -- Target: e
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: c, since a->b->c and b->d is ignored
        [ _actual1, _actual2 ] <- runOnePathSteps
            metadataTools
            (Limit 2)
            (ExpandedPattern.fromPurePattern Mock.a)
            Mock.e
            [simpleRewrite Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (sort
                [ Bottom
                , RewritePattern $ ExpandedPattern.fromPurePattern Mock.c
                ]
            )
            (sort
                [ _actual1
                , _actual2
                ]
            )

        -- Target: e
        -- Coinductive axiom: e => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: d, since a->b->d
        [ _actual1, _actual2 ] <- runOnePathSteps
            metadataTools
            (Limit 2)
            (ExpandedPattern.fromPurePattern Mock.a)
            Mock.e
            [simpleRewrite Mock.e Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (sort
                [ Bottom
                , RewritePattern $ ExpandedPattern.fromPurePattern Mock.d
                ]
            )
            (sort
                [ _actual1
                , _actual2
                ]
            )
    , testCase "Differentiated axioms" $ do
        -- Target: constr11(a)
        -- Coinductive axiom: constr11(a) => g(a)
        -- Coinductive axiom: constr11(b) => f(b)
        -- Normal axiom: constr11(a) => g(a)
        -- Normal axiom: constr11(b) => g(b)
        -- Normal axiom: constr11(c) => f(c)
        -- Normal axiom: constr11(x) => h(x)
        -- Normal axiom: constr10(x) => constr11(x)
        -- Start pattern: constr10(x)
        -- Expected:
        --   Bottom
        --   or (f(b) and x=b)
        --   or (f(c) and x=c)
        --   or (h(x) and x!=a and x!=b and x!=c )
        [ _actual1, _actual2, _actual3, _actual4 ] <-
            runOnePathSteps
                metadataTools
                (Limit 2)
                (ExpandedPattern.fromPurePattern
                    (Mock.functionalConstr10 (mkVar Mock.x))
                )
                (Mock.functionalConstr11 Mock.a)
                [ simpleRewrite (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
                , simpleRewrite (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
                ]
                [ simpleRewrite (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
                , simpleRewrite (Mock.functionalConstr11 Mock.b) (Mock.g Mock.b)
                , simpleRewrite (Mock.functionalConstr11 Mock.c) (Mock.f Mock.c)
                , simpleRewrite
                    (Mock.functionalConstr11 (mkVar Mock.y))
                    (Mock.h (mkVar Mock.y))
                , simpleRewrite
                    (Mock.functionalConstr10 (mkVar Mock.y))
                    (Mock.functionalConstr11 (mkVar Mock.y))
                ]
        assertEqualWithExplanation ""
            [ RewritePattern Predicated
                { term = Mock.f Mock.b
                , predicate = makeTruePredicate
                , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                }
            , RewritePattern Predicated
                { term = Mock.f Mock.c
                , predicate = makeTruePredicate
                , substitution = Substitution.unsafeWrap [(Mock.x, Mock.c)]
                }
            , RewritePattern Predicated
                { term = Mock.h (mkVar Mock.x)
                , predicate =  -- TODO(virgil): Better and simplification.
                    makeAndPredicate
                        (makeAndPredicate
                            (makeAndPredicate
                                (makeAndPredicate
                                    (makeNotPredicate
                                        (makeEqualsPredicate
                                            (mkVar Mock.x) Mock.a
                                        )
                                    )
                                    (makeNotPredicate
                                        (makeEqualsPredicate
                                            (mkVar Mock.x) Mock.b
                                        )
                                    )
                                )
                                (makeNotPredicate
                                    (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                                )
                            )
                            (makeNotPredicate
                                (makeEqualsPredicate (mkVar Mock.x) Mock.b)
                            )
                        )
                        (makeNotPredicate
                            (makeEqualsPredicate (mkVar Mock.x) Mock.c)
                        )
                , substitution = mempty
                }
            , Bottom
            ]
            [ _actual1
            , _actual2
            , _actual3
            , _actual4
            ]
    , testCase "Stuck pattern" $ do
        -- Target: constr11(a)
        -- Coinductive axiom: constr11(b) => f(b)
        -- Normal axiom: constr11(c) => f(c)
        -- Normal axiom: constr10(x) => constr11(x)
        -- Start pattern: constr10(x)
        -- Expected:
        --   Bottom
        --   or (f(b) and x=b)
        --   or (f(c) and x=c)
        --   Stuck (functionalConstr11(x) and x!=a and x!=b and x!=c )
        [ _actual1, _actual2, _actual3, _actual4 ] <-
            runOnePathSteps
                metadataTools
                (Limit 2)
                (ExpandedPattern.fromPurePattern
                    (Mock.functionalConstr10 (mkVar Mock.x))
                )
                (Mock.functionalConstr11 Mock.a)
                [ simpleRewrite (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
                ]
                [ simpleRewrite (Mock.functionalConstr11 Mock.c) (Mock.f Mock.c)
                , simpleRewrite
                    (Mock.functionalConstr10 (mkVar Mock.y))
                    (Mock.functionalConstr11 (mkVar Mock.y))
                ]
        assertEqualWithExplanation ""
            [ RewritePattern Predicated
                { term = Mock.f Mock.b
                , predicate = makeTruePredicate
                , substitution = Substitution.unsafeWrap [(Mock.x, Mock.b)]
                }
            , RewritePattern Predicated
                { term = Mock.f Mock.c
                , predicate = makeTruePredicate
                , substitution = Substitution.unsafeWrap [(Mock.x, Mock.c)]
                }
            , Stuck Predicated
                { term = Mock.functionalConstr11 (mkVar Mock.x)
                , predicate =
                    makeAndPredicate
                        (makeAndPredicate
                            (makeNotPredicate
                                (makeEqualsPredicate
                                    (mkVar Mock.x) Mock.a
                                )
                            )
                            (makeNotPredicate
                                (makeEqualsPredicate
                                    (mkVar Mock.x) Mock.b
                                )
                            )
                        )
                        (makeNotPredicate
                            (makeEqualsPredicate (mkVar Mock.x) Mock.c)
                        )
                , substitution = mempty
                }
            , Bottom
            ]
            [ _actual1
            , _actual2
            , _actual3
            , _actual4
            ]
    ]
  where
    symbolOrAliasSorts :: SymbolOrAliasSorts Object
    symbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    metadataTools :: MetadataTools Object StepperAttributes
    metadataTools =
        Mock.makeMetadataTools
            symbolOrAliasSorts
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.subsorts


simpleRewrite
    :: MetaOrObject level
    => CommonStepPattern level
    -> CommonStepPattern level
    -> RewriteRule level
simpleRewrite left right =
    RewriteRule RulePattern
        { left = left
        , right = right
        , requires = makeTruePredicate
        , attributes = def
        }

runSteps
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    ->  (ExecutionGraph
            ( StrategyPattern (CommonExpandedPattern level)
            , StepProof level Variable
            )
        -> Maybe (ExecutionGraph (b, StepProof level Variable))
        )
    -> (ExecutionGraph (b, StepProof level Variable) -> a)
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [Strategy (Prim (CommonExpandedPattern level) (RewriteRule level))]
    -> IO a
runSteps metadataTools graphFilter picker configuration strategy =
    (<$>) picker
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ (fromMaybe (error "Unexpected missing tree") . graphFilter)
    <$> runStrategy
        (transitionRule
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
        )
        strategy
        (RewritePattern configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty

runOnePathSteps
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> Limit Natural
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> CommonStepPattern level
    -> [RewriteRule level]
    -> [RewriteRule level]
    -> IO [StrategyPattern (CommonExpandedPattern level)]
runOnePathSteps
    metadataTools
    stepLimit
    configuration
    target
    coinductiveRewrites
    rewrites
  = do
    result <- runSteps
        metadataTools
        Just
        pickFinal
        configuration
        (Limit.takeWithin
            stepLimit
            ( onePathFirstStep expandedTarget rewrites
            : repeat
                (onePathFollowupStep
                    expandedTarget
                    coinductiveRewrites
                    rewrites
                )
            )
        )
    return (sort $ nub (map fst result))
  where
    expandedTarget = ExpandedPattern.fromPurePattern target
