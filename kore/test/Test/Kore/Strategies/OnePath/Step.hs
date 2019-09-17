module Test.Kore.Strategies.OnePath.Step
    ( test_onePathStrategy
    ) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( testCase
    )

import Data.Default
    ( def
    )
import Data.List
    ( nub
    , sort
    )
import Data.Maybe
    ( fromMaybe
    )
import Numeric.Natural
    ( Natural
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeEqualsPredicate
    , makeMultipleAndPredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Rule
    ( OnePathRule (..)
    , RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    )
import Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    )
import Kore.Step.Strategy
    ( ExecutionGraph (..)
    , Strategy
    , pickFinal
    , runStrategy
    )
import Kore.Strategies.Goal
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Syntax.Variable
    ( Variable (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Extensions


makeOnePathRule :: TermLike Variable -> TermLike Variable -> OnePathRule Variable
makeOnePathRule term dest =
    OnePathRule
    $ makeRuleFromPatterns
        (fromTermLike term)
        (fromTermLike dest)

test_onePathStrategy :: [TestTree]
test_onePathStrategy =
    [ testCase "Runs zero steps" $ do
        -- Target: a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: a
        [ actual ] <- runOnePathSteps
            (Limit 0)
            (makeOnePathRule
                Mock.a
                Mock.a
            )
            [simpleRewrite Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        assertEqualWithExplanation ""
            (ProofState.Goal $ makeOnePathRule Mock.a Mock.a)
            actual
    , testCase "Axiom priority, first step" $ do
        -- Target: a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: bottom, since a becomes bottom after removing the target.
        [ _actual ] <- runOnePathSteps
            (Limit 1)
            (makeOnePathRule Mock.a Mock.a)
            [simpleRewrite Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        assertEqualWithExplanation "" ProofState.Proven _actual

        -- Target: d
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: c, since coinductive axioms are applied only at the second
        -- step
        [ _actual ] <- runOnePathSteps
            (Limit 1)
            (makeOnePathRule Mock.a Mock.d)
            [simpleRewrite Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        assertEqualWithExplanation ""
            (ProofState.Goal $ makeOnePathRule Mock.c Mock.d)
            _actual
    , testCase "Axiom priority, second step" $ do
        -- Target: b
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: bottom, since a->b = target
        [ _actual ] <- runOnePathSteps
            (Limit 2)
            (makeOnePathRule
                Mock.a
                Mock.b
            )
            [simpleRewrite Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            ProofState.Proven
            _actual

        -- Target: e
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: c, since a->b->c and b->d is ignored
        [ _actual1 ] <- runOnePathSteps
            (Limit 2)
            (makeOnePathRule Mock.a Mock.e)
            [simpleRewrite Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (sort
                [ ProofState.Goal $ makeOnePathRule Mock.c Mock.e
                ]
            )
            (sort
                [ _actual1
                ]
            )

        -- Target: e
        -- Coinductive axiom: e => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: d, since a->b->d
        [ _actual ] <- runOnePathSteps
            (Limit 2)
            (makeOnePathRule Mock.a Mock.e)
            [simpleRewrite Mock.e Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (sort
                [ ProofState.Goal $ makeOnePathRule Mock.d Mock.e
                ]
            )
            (sort
                [ _actual
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
        --   (f(b) and x=b)
        --   or (f(c) and x=c)
        --   or (h(x) and x!=a and x!=b and x!=c )
        actual <-
            runOnePathSteps
            (Limit 2)
            (makeOnePathRule
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                (Mock.functionalConstr11 Mock.a)
            )
            [ simpleRewrite (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
            , simpleRewrite (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
            ]
            [ simpleRewrite (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
            , simpleRewrite (Mock.functionalConstr11 Mock.b) (Mock.g Mock.b)
            , simpleRewrite (Mock.functionalConstr11 Mock.c) (Mock.f Mock.c)
            , simpleRewrite
                (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
                (Mock.h (TermLike.mkElemVar Mock.y))
            , simpleRewrite
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.y))
                (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
            ]
        let expected =
                [ ProofState.Goal $ makeRuleFromPatterns
                ( Conditional
                    { term = Mock.f Mock.b
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(ElemVar Mock.x, Mock.b)]
                    }
                )
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
                , ProofState.Goal $ makeRuleFromPatterns
                ( Conditional
                    { term = Mock.f Mock.c
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap [(ElemVar Mock.x, Mock.c)]
                    }
                )
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
                , ProofState.Goal $ makeRuleFromPatterns
                ( Conditional
                    { term = Mock.h (TermLike.mkElemVar Mock.x)
                    , predicate =  -- TODO(virgil): Better and simplification.
                        makeAndPredicate
                            (makeAndPredicate
                                (makeNotPredicate
                                    (makeEqualsPredicate
                                        (TermLike.mkElemVar Mock.x) Mock.a
                                    )
                                )
                                (makeNotPredicate
                                    (makeEqualsPredicate
                                        (TermLike.mkElemVar Mock.x) Mock.b
                                    )
                                )
                            )
                            (makeNotPredicate
                                (makeEqualsPredicate (TermLike.mkElemVar Mock.x) Mock.c)
                            )
                    , substitution = mempty
                    }
                )
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
                ]
        assertEqualWithExplanation ""
            expected
            actual
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
        [ _actual1, _actual2, _actual3 ] <-
            runOnePathSteps
                (Limit 2)
                (makeOnePathRule
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ simpleRewrite (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
                ]
                [ simpleRewrite (Mock.functionalConstr11 Mock.c) (Mock.f Mock.c)
                , simpleRewrite
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.y))
                    (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
                ]
        let equalsXA = makeEqualsPredicate (TermLike.mkElemVar Mock.x) Mock.a
            equalsXB = makeEqualsPredicate (TermLike.mkElemVar Mock.x) Mock.b
            equalsXC = makeEqualsPredicate (TermLike.mkElemVar Mock.x) Mock.c
        assertEqualWithExplanation ""
            [ ProofState.Goal $ makeRuleFromPatterns
                Conditional
                    { term = Mock.f Mock.b
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.b)]
                    }
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
            , ProofState.Goal $ makeRuleFromPatterns
                Conditional
                    { term = Mock.f Mock.c
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.c)]
                    }
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
            , ProofState.GoalRemainder $ makeRuleFromPatterns
                Conditional
                    { term = Mock.functionalConstr11 (TermLike.mkElemVar Mock.x)
                    , predicate =
                        makeMultipleAndPredicate
                            [ makeNotPredicate equalsXA
                            , makeNotPredicate equalsXB
                            , makeNotPredicate equalsXC
                            ]
                    , substitution = mempty
                    }
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
            ]
            [ _actual1
            , _actual2
            , _actual3
            ]
    , testCase "Axiom with requires" $ do
        -- Target: a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) == c
        -- Start pattern: constr10(b)
        -- Expected: a | f(b) == c
        [ _actual1, _actual2 ] <- runOnePathSteps
            (Limit 2)
            (makeOnePathRule
                (Mock.functionalConstr10 Mock.b)
                Mock.a
            )
            []
            [ rewriteWithPredicate
                (Mock.functionalConstr10 Mock.b)
                Mock.a
                $ makeEqualsPredicate
                    Mock.c
                    $ Mock.f Mock.b
            ]
        assertEqualWithExplanation ""
            [ ProofState.GoalRemainder $ makeRuleFromPatterns
                ( Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate =
                        makeNotPredicate
                            $ makeEqualsPredicate
                                Mock.c
                                $ Mock.f Mock.b
                    , substitution = mempty
                    }
                )
                (fromTermLike Mock.a)
            , ProofState.Proven
            ]
            [ _actual1
            , _actual2
            ]
    , testCase "Stuck pattern simplification" $ do
        -- Target: 1
        -- Coinductive axioms: none
        -- Normal axiom: x => 1 if x<2
        -- Start pattern: 0
        [ _actual ] <-
            runOnePathSteps
                (Limit 2)
                ( makeOnePathRule
                    (Mock.builtinInt 0)
                    (Mock.builtinInt 1)
                )
                []
                [ rewriteWithPredicate
                    (TermLike.mkElemVar Mock.xInt)
                    (Mock.builtinInt 1)
                    (makeEqualsPredicate
                        (Mock.lessInt
                            (TermLike.mkElemVar Mock.xInt) (Mock.builtinInt 2)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        assertEqualWithExplanation ""
            ProofState.Proven
            _actual
    , testCase "Configuration with SMT pruning" $ do
        -- Target: a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => c | f(b) >= 0
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Start pattern: constr10(b) | f(b) < 0
        -- Expected: a | f(b) < 0
        [ _actual1, _actual2 ] <- runOnePathSteps
            (Limit 1)
            (makeRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate = makeEqualsPredicate
                        (Mock.lessInt
                            (Mock.fTestInt Mock.b)
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                    , substitution = mempty
                    }
                )
                (fromTermLike Mock.a)
            )
            []
            [ rewriteWithPredicate
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                Mock.a
                (makeEqualsPredicate
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            , rewriteWithPredicate
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                Mock.c
                (makeEqualsPredicate
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool False)
                )
            ]
        assertEqualWithExplanation ""
            [ ProofState.Goal $ makeRuleFromPatterns
                ( Conditional
                    { term = Mock.a
                    , predicate =
                        makeEqualsPredicate
                            (Mock.lessInt
                                (Mock.fTestInt Mock.b)
                                (Mock.builtinInt 0)
                            )
                            (Mock.builtinBool True)
                    , substitution = mempty
                    }
                )
                (fromTermLike Mock.a)
            , ProofState.Proven ]
            [ _actual1, _actual2 ]
    , testCase "SMT pruning in the first step" $ do
        -- Target: a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Start pattern: constr10(b) | f(b) < 0
        -- Expected: a | f(b) < 0
        [ _actual1, _actual2 ] <- runOnePathSteps
            (Limit 1)
            (makeRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate = makeEqualsPredicate
                        (Mock.lessInt
                            (Mock.fTestInt Mock.b)
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                    , substitution = mempty
                    }
                )
                (Pattern.fromTermLike Mock.a)
            )
            []
            [ rewriteWithPredicate
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                Mock.a
                (makeEqualsPredicate
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            ]
        assertEqualWithExplanation ""
            [ ProofState.Goal $ makeRuleFromPatterns
                ( Conditional
                    { term = Mock.a
                    , predicate =
                        makeEqualsPredicate
                            (Mock.lessInt
                                (Mock.fTestInt Mock.b)
                                (Mock.builtinInt 0)
                            )
                            (Mock.builtinBool True)
                    , substitution = mempty
                    }
                )
                (Pattern.fromTermLike Mock.a)
            , ProofState.Proven
            ]
            [ _actual1, _actual2 ]
    ]

simpleRewrite
    :: TermLike Variable
    -> TermLike Variable
    -> Rule (OnePathRule Variable)
simpleRewrite left right =
    OnePathRewriteRule
    $ RewriteRule RulePattern
        { left = left
        , right = right
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

rewriteWithPredicate
    :: TermLike Variable
    -> TermLike Variable
    -> Syntax.Predicate Variable
    -> Rule (OnePathRule Variable)
rewriteWithPredicate left right predicate =
    OnePathRewriteRule
    $ RewriteRule RulePattern
        { left = left
        , right = right
        , requires = predicate
        , ensures = makeTruePredicate
        , attributes = def
        }

runSteps
    :: ( ExecutionGraph
            (ProofState (OnePathRule Variable) (OnePathRule Variable))
            (Rule (OnePathRule Variable))
       -> Maybe (ExecutionGraph b c)
       )
    -> (ExecutionGraph b c -> a)
    -> OnePathRule Variable
    -- ^left-hand-side of unification
    -> [Strategy (Prim (OnePathRule Variable))]
    -> IO a
runSteps graphFilter picker configuration strategy' =
    (<$>) picker
    $ runSimplifier mockEnv
    $ fromMaybe (error "Unexpected missing tree") . graphFilter
    <$> runStrategy transitionRule strategy' (ProofState.Goal configuration)
  where
    mockEnv = Mock.env

runOnePathSteps
    :: Limit Natural
    -> OnePathRule Variable
    -- ^left-hand-side of unification
    -> [Rule (OnePathRule Variable)]
    -> [Rule (OnePathRule Variable)]
    -> IO [ProofState (OnePathRule Variable) (OnePathRule Variable)]
runOnePathSteps
    stepLimit
    goal
    coinductiveRewrites
    rewrites
  = do
    result <- runSteps
        Just
        pickFinal
        goal
        (Limit.takeWithin
            stepLimit
            ( onePathFirstStep rewrites
            : repeat
                (onePathFollowupStep
                    coinductiveRewrites
                    rewrites
                )
            )
        )
    return (sort $ nub result)
