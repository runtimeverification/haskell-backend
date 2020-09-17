module Test.Kore.Strategies.OnePath.Step
    ( test_onePathStrategy
    ) where

import Prelude.Kore

import Test.Tasty

import Data.Coerce
    ( coerce
    )
import Data.Default
    ( def
    )
import qualified Data.Foldable as Foldable
import Data.List.Extra
    ( groupSortOn
    , nub
    , sort
    )
import Numeric.Natural
    ( Natural
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import qualified Kore.Attribute.Axiom as Attribute.Axiom
import Kore.Rewriting.RewritingVariable

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeEqualsPredicate
    , makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    , OnePathRule (..)
    , ReachabilityRule (..)
    )
import Kore.Step.RulePattern
    ( RulePattern (..)
    , injectTermIntoRHS
    , mkRewritingRule
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

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

type TermLike' = TermLike VariableName
type Pattern' = Pattern VariableName
type Predicate' = Predicate VariableName

makeOnePathGoal
    :: TermLike'
    -> TermLike'
    -> OnePathRule
makeOnePathGoal
    (TermLike.mapVariables (pure mkConfigVariable) -> left)
    (TermLike.mapVariables (pure mkConfigVariable) -> right)
  =
    OnePathRule
    $ ClaimPattern
            { left =
                Pattern.fromTermAndPredicate
                    left
                    makeTruePredicate
            , right =
                Pattern.fromTermAndPredicate
                    right
                    makeTruePredicate
                & OrPattern.fromPattern
            , existentials = []
            , attributes = def
            }

makeOnePathRule
    :: TermLike'
    -> TermLike'
    -> OnePathRule
makeOnePathRule
    (TermLike.mapVariables (pure mkRuleVariable) -> left)
    (TermLike.mapVariables (pure mkRuleVariable) -> right)
  =
    OnePathRule
    $ ClaimPattern
            { left =
                Pattern.fromTermAndPredicate
                    left
                    makeTruePredicate
            , right =
                Pattern.fromTermAndPredicate
                    right
                    makeTruePredicate
                & OrPattern.fromPattern
            , existentials = []
            , attributes = def
            }

makeOnePathGoalFromPatterns
    :: Pattern'
    -> Pattern'
    -> OnePathRule
makeOnePathGoalFromPatterns
    (Pattern.mapVariables (pure mkConfigVariable) -> left)
    (Pattern.mapVariables (pure mkConfigVariable) -> right)
  =
    OnePathRule
    $ ClaimPattern
            { left
            , right = OrPattern.fromPattern right
            , existentials = []
            , attributes = def
            }

makeReachabilityOnePathGoal
    :: TermLike'
    -> TermLike'
    -> ReachabilityRule
makeReachabilityOnePathGoal term dest =
    OnePath (makeOnePathGoal term dest)

makeReachabilityOnePathRule
    :: TermLike'
    -> TermLike'
    -> ReachabilityRule
makeReachabilityOnePathRule term dest =
    OnePath (makeOnePathRule term dest)

test_onePathStrategy :: [TestTree]
test_onePathStrategy =
    [ testCase "Runs zero steps" $ do
        -- Goal: a => a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Expected: a
        [ actual ] <- runOnePathSteps
            Unlimited
            (Limit 0)
            (makeOnePathGoal
                Mock.a
                Mock.a
            )
            [makeOnePathRule Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        [ actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 0)
            (makeReachabilityOnePathGoal
                Mock.a
                Mock.a
            )
            [makeReachabilityOnePathRule Mock.a Mock.b]
            [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual ""
            (ProofState.Goal $ makeOnePathRule Mock.a Mock.a)
            actual
        assertEqual "onepath == reachability onepath"
            (fmap OnePath actual)
            actualReach
    , testCase "Axiom priority, first step" $ do
        -- Goal: a => a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Expected: bottom, since a becomes bottom after removing the target.
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (makeOnePathGoal Mock.a Mock.a)
            [makeOnePathRule Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        [ _actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (makeReachabilityOnePathGoal Mock.a Mock.a)
            [makeReachabilityOnePathRule Mock.a Mock.b]
            [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual "" ProofState.Proven _actual
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach

        -- Goal: a => d
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Expected: c, since coinductive axioms are applied only at the second
        -- step
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (makeOnePathGoal Mock.a Mock.d)
            [makeOnePathRule Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        [ _actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (makeReachabilityOnePathGoal Mock.a Mock.d)
            [makeReachabilityOnePathRule Mock.a Mock.b]
            [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual ""
            (ProofState.GoalRewritten $ makeOnePathRule Mock.c Mock.d)
            _actual
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Axiom priority, second step" $ do
        -- Goal: a => b
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Expected: bottom, since a->b = target
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeOnePathGoal
                Mock.a
                Mock.b
            )
            [makeOnePathRule Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        [ _actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeReachabilityOnePathGoal
                Mock.a
                Mock.b
            )
            [makeReachabilityOnePathRule Mock.b Mock.c]
            [ simpleReachabilityRewrite Mock.b Mock.d
            , simpleReachabilityRewrite Mock.a Mock.b
            ]
        assertEqual ""
            ProofState.Proven
            _actual
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach

        -- Goal: a => e
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Expected: c, since a->b->c and b->d is ignored
        [ _actual1 ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeOnePathGoal Mock.a Mock.e)
            [makeOnePathRule Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        [ _actual1Reach ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeReachabilityOnePathGoal Mock.a Mock.e)
            [makeReachabilityOnePathRule Mock.b Mock.c]
            [ simpleReachabilityRewrite Mock.b Mock.d
            , simpleReachabilityRewrite Mock.a Mock.b
            ]
        assertEqual ""
            (sort
                [ ProofState.GoalRewritten $ makeOnePathRule Mock.c Mock.e
                ]
            )
            (sort
                [ _actual1
                ]
            )
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual1)
            _actual1Reach

        -- Goal: a => e
        -- Coinductive axiom: e => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Expected: d, since a->b->d
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeOnePathGoal Mock.a Mock.e)
            [makeOnePathRule Mock.e Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        [ _actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeReachabilityOnePathGoal Mock.a Mock.e)
            [makeReachabilityOnePathRule Mock.e Mock.c]
            [ simpleReachabilityRewrite Mock.b Mock.d
            , simpleReachabilityRewrite Mock.a Mock.b
            ]
        assertEqual ""
            (sort
                [ ProofState.GoalRewritten $ makeOnePathRule Mock.d Mock.e
                ]
            )
            (sort
                [ _actual
                ]
            )
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Differentiated axioms" $ do
        -- Goal: constr10(x) => constr11(a)
        -- Coinductive axiom: constr11(a) => g(a)
        -- Coinductive axiom: constr11(b) => f(b)
        -- Normal axiom: constr11(a) => g(a)
        -- Normal axiom: constr11(b) => g(b)
        -- Normal axiom: constr11(c) => f(c)
        -- Normal axiom: constr11(x) => h(x)
        -- Normal axiom: constr10(x) => constr11(x)
        -- Expected:
        --   Stuck after removing the destination during
        --   the second step.
        --
        --   If remove destination didn't
        --   detect that the conditions do not meet, then
        --   the configuration would have resulted in:
        --      (f(b) and x=b)
        --      or (f(c) and x=c)
        --      or (h(x) and x!=a and x!=b and x!=c )
        actual@[ _actual ] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeOnePathRule (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
                , makeOnePathRule (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
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
        actualReach <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeReachabilityOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeReachabilityOnePathRule
                    (Mock.functionalConstr11 Mock.a)
                    (Mock.g Mock.a)
                , makeReachabilityOnePathRule
                    (Mock.functionalConstr11 Mock.b)
                    (Mock.f Mock.b)
                ]
                [ simpleReachabilityRewrite
                    (Mock.functionalConstr11 Mock.a)
                    (Mock.g Mock.a)
                , simpleReachabilityRewrite
                    (Mock.functionalConstr11 Mock.b)
                    (Mock.g Mock.b)
                , simpleReachabilityRewrite
                    (Mock.functionalConstr11 Mock.c)
                    (Mock.f Mock.c)
                , simpleReachabilityRewrite
                    (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
                    (Mock.h (TermLike.mkElemVar Mock.y))
                , simpleReachabilityRewrite
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.y))
                    (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
                ]
        let expectedGoal =
                makeOnePathGoalFromPatterns
                    Conditional
                        { term =
                            Mock.functionalConstr11 (TermLike.mkElemVar Mock.x)
                        , predicate =
                            makeNotPredicate
                                ( makeEqualsPredicate
                                    (TermLike.mkElemVar Mock.x)
                                    Mock.a
                                )
                        , substitution = mempty
                        }
                    (Pattern.fromTermLike $ Mock.functionalConstr11 Mock.a)
        assertStuck expectedGoal actual actualReach
    , testCase "Stuck pattern" $ do
        -- Goal: constr10(x) => constr11(a)
        -- Coinductive axiom: constr11(b) => f(b)
        -- Normal axiom: constr11(c) => f(c)
        -- Normal axiom: constr10(x) => constr11(x)
        -- Expected:
        --   Stuck after removing the destination during
        --   the second step.
        --
        --   If remove destination didn't
        --   detect that the conditions do not meet, then
        --   the configuration would have resulted in:
        --      Proven
        --      or (f(b) and x=b)
        --      or (f(c) and x=c)
        --      GoalRemainder (functionalConstr11(x) and x!=a and x!=b and x!=c )
        actual@[ _actual ] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeOnePathRule (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
                ]
                [ simpleRewrite (Mock.functionalConstr11 Mock.c) (Mock.f Mock.c)
                , simpleRewrite
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.y))
                    (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
                ]
        actualReach <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeReachabilityOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeReachabilityOnePathRule
                    (Mock.functionalConstr11 Mock.b)
                    (Mock.f Mock.b)
                ]
                [ simpleReachabilityRewrite
                    (Mock.functionalConstr11 Mock.c)
                    (Mock.f Mock.c)
                , simpleReachabilityRewrite
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.y))
                    (Mock.functionalConstr11 (TermLike.mkElemVar Mock.y))
                ]
        let expectedGoal =
                makeOnePathGoalFromPatterns
                    Conditional
                        { term =
                            Mock.functionalConstr11 (TermLike.mkElemVar Mock.x)
                        , predicate =
                            makeNotPredicate
                                ( makeEqualsPredicate
                                    (TermLike.mkElemVar Mock.x)
                                    Mock.a
                                )
                        , substitution = mempty
                        }
                    (Pattern.fromTermLike $ Mock.functionalConstr11 Mock.a)
        assertStuck expectedGoal actual actualReach
    , testCase "Axiom with requires" $ do
        -- Goal:  constr10(b) => a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) == c
        -- Expected: a | f(b) == c
        actual@[ _actual1, _actual2 ] <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeOnePathGoal
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
        actualReach <- runOnePathSteps
            Unlimited
            (Limit 2)
            (makeReachabilityOnePathGoal
                (Mock.functionalConstr10 Mock.b)
                Mock.a
            )
            []
            [ rewriteReachabilityWithPredicate
                (Mock.functionalConstr10 Mock.b)
                Mock.a
                $ makeEqualsPredicate
                    Mock.c
                    $ Mock.f Mock.b
            ]
        assertEqual ""
            [ ProofState.GoalStuck
            $ makeOnePathGoalFromPatterns
                Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate =
                        makeNotPredicate
                            $ makeEqualsPredicate
                                Mock.c
                                $ Mock.f Mock.b
                    , substitution = mempty
                    }
                (fromTermLike Mock.a)
            , ProofState.Proven
            ]
            [ _actual1
            , _actual2
            ]
        assertEqual "onepath == reachability onepath"
            (fmap (fmap OnePath) actual)
            actualReach
    , testCase "Stuck pattern simplification" $ do
        -- Goal: 0 => 1
        -- Coinductive axioms: none
        -- Normal axiom: x => 1 if x<2
        [ _actual ] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeOnePathGoal
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
        [ _actualReach ] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeReachabilityOnePathGoal
                    (Mock.builtinInt 0)
                    (Mock.builtinInt 1)
                )
                []
                [ rewriteReachabilityWithPredicate
                    (TermLike.mkElemVar Mock.xInt)
                    (Mock.builtinInt 1)
                    (makeEqualsPredicate
                        (Mock.lessInt
                            (TermLike.mkElemVar Mock.xInt) (Mock.builtinInt 2)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        assertEqual ""
            ProofState.Proven
            _actual
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Configuration with SMT pruning" $ do
        -- Goal: constr10(b) | f(b) < 0  =>  a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => c | f(b) >= 0
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Expected: a | f(b) < 0
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (makeOnePathGoalFromPatterns
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
        [ _actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (OnePath $ makeOnePathGoalFromPatterns
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
            [ rewriteReachabilityWithPredicate
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                Mock.a
                (makeEqualsPredicate
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            , rewriteReachabilityWithPredicate
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
        assertEqual ""
            [ ProofState.GoalRewritten $ makeOnePathGoalFromPatterns
                Conditional
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
                (fromTermLike Mock.a)
            ]
            [ _actual
            ]
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Stuck with SMT pruning" $ do
        -- Goal: constr10(b) | f(b) < 0  =>  a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Expected: a | f(b) < 0
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (makeOnePathGoalFromPatterns
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
            ]
        [ _actualReach ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            (OnePath $ makeOnePathGoalFromPatterns
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
            [ rewriteReachabilityWithPredicate
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
        assertEqual ""
            [ ProofState.GoalRewritten $ makeOnePathGoalFromPatterns
                Conditional
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
                (fromTermLike Mock.a)
            ]
            [ _actual ]
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Goal stuck after remove destination" $ do
        -- Goal: X && X = a => X && X != a
        -- Coinductive axiom: -
        -- Normal axiom: -
        -- Expected: stuck, since the terms unify but the conditions do not
        let left =
                Pattern.withCondition
                    (TermLike.mkElemVar Mock.x)
                    (Condition.fromPredicate
                        (makeEqualsPredicate
                            (TermLike.mkElemVar Mock.x)
                            Mock.a
                        )
                    )
            left' =
                Pattern.withCondition
                    Mock.a
                    (Condition.assign (inject Mock.x) Mock.a)
            right =
                Pattern.withCondition
                    (TermLike.mkElemVar Mock.x)
                    (Condition.fromPredicate $ makeNotPredicate
                        (makeEqualsPredicate
                            (TermLike.mkElemVar Mock.x)
                            Mock.a
                        )
                    )
            original = makeOnePathGoalFromPatterns left right
            expect = makeOnePathGoalFromPatterns left' right
        [ _actual ] <- runOnePathSteps
            Unlimited
            (Limit 1)
            original
            []
            []
        assertEqual "" (ProofState.GoalStuck expect) _actual
    ]

simpleRewrite
    :: TermLike'
    -> TermLike'
    -> Rule OnePathRule
simpleRewrite left right =
    OnePathRewriteRule . mkRewritingRule
    $ RewriteRule RulePattern
        { left = left
        , antiLeft = Nothing
        , requires = makeTruePredicate
        , rhs = injectTermIntoRHS right
        , attributes = def
        }

simpleReachabilityRewrite
    :: TermLike'
    -> TermLike'
    -> Rule ReachabilityRule
simpleReachabilityRewrite left right =
    coerce (simpleRewrite left right)

rewriteWithPredicate
    :: TermLike'
    -> TermLike'
    -> Predicate'
    -> Rule OnePathRule
rewriteWithPredicate left right predicate =
    OnePathRewriteRule . mkRewritingRule
    $ RewriteRule RulePattern
        { left = left
        , antiLeft = Nothing
        , requires = predicate
        , rhs = injectTermIntoRHS right
        , attributes = def
        }

rewriteReachabilityWithPredicate
    :: TermLike'
    -> TermLike'
    -> Predicate'
    -> Rule ReachabilityRule
rewriteReachabilityWithPredicate left right predicate =
    coerce (rewriteWithPredicate left right predicate)

runSteps
    :: Goal goal
    => Limit Natural
    -> ( ExecutionGraph (ProofState.ProofState goal) (AppliedRule goal)
       -> Maybe (ExecutionGraph b c)
       )
    -> (ExecutionGraph b c -> a)
    -> [goal]
    -> [[Rule goal]]
    -> goal
    -- ^left-hand-side of unification
    -> [Strategy Prim]
    -> IO a
runSteps
    breadthLimit
    graphFilter
    picker
    claims
    axiomGroups
    configuration
    strategy'
  =
    (<$>) picker
    $ runSimplifier mockEnv
    $ fromMaybe (error "Unexpected missing tree") . graphFilter
    <$> runStrategy
            breadthLimit
            (transitionRule claims axiomGroups)
            strategy'
            (ProofState.Goal configuration)
  where
    mockEnv = Mock.env

runOnePathSteps
    :: Goal goal
    => Ord goal
    => From (Rule goal) Attribute.Axiom.PriorityAttributes
    => Limit Natural
    -> Limit Natural
    -> goal
    -- ^left-hand-side of unification
    -> [goal]
    -> [Rule goal]
    -> IO [ProofState.ProofState goal]
runOnePathSteps
    breadthLimit
    depthLimit
    goal
    coinductiveRewrites
    rewrites
  = do
    result <- runSteps
        breadthLimit
        Just
        pickFinal
        coinductiveRewrites
        (groupSortOn Attribute.Axiom.getPriorityOfAxiom rewrites)
        goal
        (Limit.takeWithin depthLimit (Foldable.toList strategy))
    return (sort $ nub result)

assertStuck
    :: OnePathRule
    -> [ProofState.ProofState OnePathRule]
    -> [ProofState.ProofState ReachabilityRule]
    -> IO ()
assertStuck expectedGoal actual actualReach = do
    assertEqual "as one-path claim" [ ProofState.GoalStuck expectedGoal ] actual
    assertEqual "as reachability claim" (asOnePath actual) actualReach
  where
    asOnePath = (fmap . fmap) OnePath
