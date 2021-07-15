module Test.Kore.Reachability.OnePathStrategy (
    test_onePathStrategy,
) where

import Data.Coerce (
    coerce,
 )
import Data.Default (
    def,
 )
import Data.Limit (
    Limit (..),
 )
import qualified Data.Limit as Limit
import Data.List.Extra (
    groupSortOn,
    nub,
    sort,
 )
import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeEqualsPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability
import qualified Kore.Reachability.ClaimState as ClaimState
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
 )
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    RulePattern (..),
    injectTermIntoRHS,
    mkRewritingRule,
 )
import Kore.Rewrite.Strategy (
    ExecutionGraph (..),
    Strategy,
    pickFinal,
    runStrategy,
 )
import Kore.Syntax.Variable
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

type TermLike' = TermLike VariableName
type Pattern' = Pattern VariableName
type Predicate' = Predicate VariableName

makeOnePathGoal ::
    TermLike' ->
    TermLike' ->
    OnePathClaim
makeOnePathGoal
    (mkRewritingTerm -> left)
    (mkRewritingTerm -> right) =
        OnePathClaim $
            ClaimPattern
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

makeOnePathClaim ::
    TermLike' ->
    TermLike' ->
    OnePathClaim
makeOnePathClaim
    (TermLike.mapVariables (pure mkRuleVariable) -> left)
    (TermLike.mapVariables (pure mkRuleVariable) -> right) =
        OnePathClaim $
            ClaimPattern
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

makeOnePathGoalFromPatterns ::
    Pattern' ->
    Pattern' ->
    OnePathClaim
makeOnePathGoalFromPatterns
    (Pattern.mapVariables (pure mkConfigVariable) -> left)
    (Pattern.mapVariables (pure mkConfigVariable) -> right) =
        OnePathClaim $
            ClaimPattern
                { left
                , right = OrPattern.fromPattern right
                , existentials = []
                , attributes = def
                }

makeReachabilityOnePathGoal ::
    TermLike' ->
    TermLike' ->
    SomeClaim
makeReachabilityOnePathGoal term dest =
    OnePath (makeOnePathGoal term dest)

makeReachabilityOnePathClaim ::
    TermLike' ->
    TermLike' ->
    SomeClaim
makeReachabilityOnePathClaim term dest =
    OnePath (makeOnePathClaim term dest)

test_onePathStrategy :: [TestTree]
test_onePathStrategy =
    [ testCase "Runs zero steps" $ do
        -- Goal: a => a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Expected: a
        [actual] <-
            runOnePathSteps
                Unlimited
                (Limit 0)
                ( makeOnePathGoal
                    Mock.a
                    Mock.a
                )
                [makeOnePathClaim Mock.a Mock.b]
                [simpleRewrite Mock.a Mock.c]
        [actualReach] <-
            runOnePathSteps
                Unlimited
                (Limit 0)
                ( makeReachabilityOnePathGoal
                    Mock.a
                    Mock.a
                )
                [makeReachabilityOnePathClaim Mock.a Mock.b]
                [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual
            ""
            (Claimed $ makeOnePathClaim Mock.a Mock.a)
            actual
        assertEqual
            "onepath == reachability onepath"
            (fmap OnePath actual)
            actualReach
    , testCase "Axiom priority, first step" $ do
        -- Goal: a => a
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Expected: bottom, since a becomes bottom after removing the target.
        [_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                (makeOnePathGoal Mock.a Mock.a)
                [makeOnePathClaim Mock.a Mock.b]
                [simpleRewrite Mock.a Mock.c]
        [_actualReach] <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                (makeReachabilityOnePathGoal Mock.a Mock.a)
                [makeReachabilityOnePathClaim Mock.a Mock.b]
                [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual "" ClaimState.Proven _actual
        assertEqual
            "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach

        -- Goal: a => d
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Expected: c, since coinductive axioms are applied only at the second
        -- step
        [_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                (makeOnePathGoal Mock.a Mock.d)
                [makeOnePathClaim Mock.a Mock.b]
                [simpleRewrite Mock.a Mock.c]
        [_actualReach] <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                (makeReachabilityOnePathGoal Mock.a Mock.d)
                [makeReachabilityOnePathClaim Mock.a Mock.b]
                [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual
            ""
            (Rewritten $ makeOnePathClaim Mock.c Mock.d)
            _actual
        assertEqual
            "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Axiom priority, second step" $ do
        -- Goal: a => b
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Expected: bottom, since a->b = target
        [_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeOnePathGoal
                    Mock.a
                    Mock.b
                )
                [makeOnePathClaim Mock.b Mock.c]
                [ simpleRewrite Mock.b Mock.d
                , simpleRewrite Mock.a Mock.b
                ]
        [_actualReach] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeReachabilityOnePathGoal
                    Mock.a
                    Mock.b
                )
                [makeReachabilityOnePathClaim Mock.b Mock.c]
                [ simpleReachabilityRewrite Mock.b Mock.d
                , simpleReachabilityRewrite Mock.a Mock.b
                ]
        assertEqual
            ""
            ClaimState.Proven
            _actual
        assertEqual
            "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach

        -- Goal: a => e
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Expected: c, since a->b->c and b->d is ignored
        [_actual1] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeOnePathGoal Mock.a Mock.e)
                [makeOnePathClaim Mock.b Mock.c]
                [ simpleRewrite Mock.b Mock.d
                , simpleRewrite Mock.a Mock.b
                ]
        [_actual1Reach] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeReachabilityOnePathGoal Mock.a Mock.e)
                [makeReachabilityOnePathClaim Mock.b Mock.c]
                [ simpleReachabilityRewrite Mock.b Mock.d
                , simpleReachabilityRewrite Mock.a Mock.b
                ]
        assertEqual
            ""
            ( sort
                [ Rewritten $ makeOnePathClaim Mock.c Mock.e
                ]
            )
            ( sort
                [ _actual1
                ]
            )
        assertEqual
            "onepath == reachability onepath"
            (fmap OnePath _actual1)
            _actual1Reach

        -- Goal: a => e
        -- Coinductive axiom: e => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Expected: d, since a->b->d
        [_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeOnePathGoal Mock.a Mock.e)
                [makeOnePathClaim Mock.e Mock.c]
                [ simpleRewrite Mock.b Mock.d
                , simpleRewrite Mock.a Mock.b
                ]
        [_actualReach] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                (makeReachabilityOnePathGoal Mock.a Mock.e)
                [makeReachabilityOnePathClaim Mock.e Mock.c]
                [ simpleReachabilityRewrite Mock.b Mock.d
                , simpleReachabilityRewrite Mock.a Mock.b
                ]
        assertEqual
            ""
            ( sort
                [ Rewritten $ makeOnePathClaim Mock.d Mock.e
                ]
            )
            ( sort
                [ _actual
                ]
            )
        assertEqual
            "onepath == reachability onepath"
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
        --   Stuck after checking the implication during
        --   the second step.
        --
        --   If the check implication transition didn't
        --   detect that the conditions do not meet, then
        --   the configuration would have resulted in:
        --      (f(b) and x=b)
        --      or (f(c) and x=c)
        --      or (h(x) and x!=a and x!=b and x!=c )
        actual@[_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeOnePathClaim (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
                , makeOnePathClaim (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
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
                ( makeReachabilityOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeReachabilityOnePathClaim
                    (Mock.functionalConstr11 Mock.a)
                    (Mock.g Mock.a)
                , makeReachabilityOnePathClaim
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
        actual@[_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeOnePathClaim (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
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
                ( makeReachabilityOnePathGoal
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    (Mock.functionalConstr11 Mock.a)
                )
                [ makeReachabilityOnePathClaim
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
        actual@[_actual1, _actual2] <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeOnePathGoal
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
        actualReach <-
            runOnePathSteps
                Unlimited
                (Limit 2)
                ( makeReachabilityOnePathGoal
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
        assertEqual
            ""
            [ Stuck $
                makeOnePathGoalFromPatterns
                    Conditional
                        { term = Mock.functionalConstr10 Mock.b
                        , predicate =
                            makeNotPredicate $
                                makeEqualsPredicate
                                    Mock.c
                                    $ Mock.f Mock.b
                        , substitution = mempty
                        }
                    (fromTermLike Mock.a)
            , Proven
            ]
            [ _actual1
            , _actual2
            ]
        assertEqual
            "onepath == reachability onepath"
            (fmap (fmap OnePath) actual)
            actualReach
    , testCase "Stuck pattern simplification" $ do
        -- Goal: 0 => 1
        -- Coinductive axioms: none
        -- Normal axiom: x => 1 if x<2
        [_actual] <-
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
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (TermLike.mkElemVar Mock.xInt)
                            (Mock.builtinInt 2)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        [_actualReach] <-
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
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (TermLike.mkElemVar Mock.xInt)
                            (Mock.builtinInt 2)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        assertEqual "" Proven _actual
        assertEqual
            "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    , testCase "Configuration with SMT pruning" $ do
        -- Goal: constr10(b) | f(b) < 0  =>  a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => c | f(b) >= 0
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Expected: a | f(b) < 0
        _actual <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                ( makeOnePathGoalFromPatterns
                    Conditional
                        { term = Mock.functionalConstr10 Mock.b
                        , predicate =
                            makeEqualsPredicate
                                ( Mock.lessInt
                                    (Mock.fTestInt Mock.b)
                                    (Mock.builtinInt 0)
                                )
                                (Mock.builtinBool True)
                        , substitution = mempty
                        }
                    (fromTermLike Mock.a)
                )
                []
                [ rewriteWithPredicate
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    Mock.a
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                    )
                , rewriteWithPredicate
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    Mock.c
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool False)
                    )
                ]
        _actualReach <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                ( OnePath $
                    makeOnePathGoalFromPatterns
                        Conditional
                            { term = Mock.functionalConstr10 Mock.b
                            , predicate =
                                makeEqualsPredicate
                                    ( Mock.lessInt
                                        (Mock.fTestInt Mock.b)
                                        (Mock.builtinInt 0)
                                    )
                                    (Mock.builtinBool True)
                            , substitution = mempty
                            }
                        (fromTermLike Mock.a)
                )
                []
                [ rewriteReachabilityWithPredicate
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    Mock.a
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                    )
                , rewriteReachabilityWithPredicate
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    Mock.c
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool False)
                    )
                ]
        assertEqual
            ""
            [ Rewritten $
                makeOnePathGoalFromPatterns
                    Conditional
                        { term = Mock.a
                        , predicate =
                            makeEqualsPredicate
                                (Mock.builtinBool True)
                                ( Mock.lessInt
                                    (Mock.fTestInt Mock.b)
                                    (Mock.builtinInt 0)
                                )
                        , substitution = mempty
                        }
                    (fromTermLike Mock.a)
            ]
            _actual
        assertEqual
            "onepath == reachability onepath"
            ((fmap . fmap) OnePath _actual)
            _actualReach
    , testCase "Stuck with SMT pruning" $ do
        -- Goal: constr10(b) | f(b) < 0  =>  a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) < 0
        -- Expected: a | f(b) < 0
        _actual <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                ( makeOnePathGoalFromPatterns
                    Conditional
                        { term = Mock.functionalConstr10 Mock.b
                        , predicate =
                            makeEqualsPredicate
                                ( Mock.lessInt
                                    (Mock.fTestInt Mock.b)
                                    (Mock.builtinInt 0)
                                )
                                (Mock.builtinBool True)
                        , substitution = mempty
                        }
                    (fromTermLike Mock.a)
                )
                []
                [ rewriteWithPredicate
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    Mock.a
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        _actualReach <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                ( OnePath $
                    makeOnePathGoalFromPatterns
                        Conditional
                            { term = Mock.functionalConstr10 Mock.b
                            , predicate =
                                makeEqualsPredicate
                                    ( Mock.lessInt
                                        (Mock.fTestInt Mock.b)
                                        (Mock.builtinInt 0)
                                    )
                                    (Mock.builtinBool True)
                            , substitution = mempty
                            }
                        (fromTermLike Mock.a)
                )
                []
                [ rewriteReachabilityWithPredicate
                    (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                    Mock.a
                    ( makeEqualsPredicate
                        ( Mock.lessInt
                            (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                            (Mock.builtinInt 0)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        assertEqual
            ""
            [ Rewritten $
                makeOnePathGoalFromPatterns
                    Conditional
                        { term = Mock.a
                        , predicate =
                            makeEqualsPredicate
                                (Mock.builtinBool True)
                                ( Mock.lessInt
                                    (Mock.fTestInt Mock.b)
                                    (Mock.builtinInt 0)
                                )
                        , substitution = mempty
                        }
                    (fromTermLike Mock.a)
            ]
            _actual
        assertEqual
            "onepath == reachability onepath"
            ((fmap . fmap) OnePath _actual)
            _actualReach
    , testCase "RHS simplification, checkImplication detects \\bottom RHS" $ do
        -- Goal: X && X = a => X && X != a
        -- Coinductive axiom: -
        -- Normal axiom: -
        -- Expected: stuck
        let left =
                Pattern.withCondition
                    (TermLike.mkElemVar Mock.x)
                    ( Condition.fromPredicate
                        ( makeEqualsPredicate
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
                    ( Condition.fromPredicate $
                        makeNotPredicate
                            ( makeEqualsPredicate
                                (TermLike.mkElemVar Mock.x)
                                Mock.a
                            )
                    )
            right' = Pattern.bottom
            original = makeOnePathGoalFromPatterns left right
            expect = makeOnePathGoalFromPatterns left' right'
        [_actual] <-
            runOnePathSteps
                Unlimited
                (Limit 1)
                original
                []
                []
        assertEqual "" (Stuck expect) _actual
    ]

simpleRewrite ::
    TermLike' ->
    TermLike' ->
    Rule OnePathClaim
simpleRewrite left right =
    OnePathRewriteRule . mkRewritingRule $
        RewriteRule
            RulePattern
                { left = left
                , antiLeft = Nothing
                , requires = makeTruePredicate
                , rhs = injectTermIntoRHS right
                , attributes = def
                }

simpleReachabilityRewrite ::
    TermLike' ->
    TermLike' ->
    Rule SomeClaim
simpleReachabilityRewrite left right =
    coerce (simpleRewrite left right)

rewriteWithPredicate ::
    TermLike' ->
    TermLike' ->
    Predicate' ->
    Rule OnePathClaim
rewriteWithPredicate left right predicate =
    OnePathRewriteRule . mkRewritingRule $
        RewriteRule
            RulePattern
                { left = left
                , antiLeft = Nothing
                , requires = predicate
                , rhs = injectTermIntoRHS right
                , attributes = def
                }

rewriteReachabilityWithPredicate ::
    TermLike' ->
    TermLike' ->
    Predicate' ->
    Rule SomeClaim
rewriteReachabilityWithPredicate left right predicate =
    coerce (rewriteWithPredicate left right predicate)

runSteps ::
    Claim claim =>
    Limit Natural ->
    ( ExecutionGraph (ClaimState.ClaimState claim) (AppliedRule claim) ->
      Maybe (ExecutionGraph b c)
    ) ->
    (ExecutionGraph b c -> a) ->
    [claim] ->
    [[Rule claim]] ->
    -- |left-hand-side of unification
    claim ->
    [Strategy Prim] ->
    IO a
runSteps
    breadthLimit
    graphFilter
    picker
    claims
    axiomGroups
    configuration
    strategy' =
        (<$>) picker $
            runSimplifierSMT mockEnv $
                fromMaybe (error "Unexpected missing tree") . graphFilter
                    <$> runStrategy
                        breadthLimit
                        (transitionRule claims axiomGroups)
                        strategy'
                        (Claimed configuration)
      where
        mockEnv = Mock.env

runOnePathSteps ::
    Claim claim =>
    Ord claim =>
    From (Rule claim) Attribute.Axiom.PriorityAttributes =>
    Limit Natural ->
    Limit Natural ->
    -- |left-hand-side of unification
    claim ->
    [claim] ->
    [Rule claim] ->
    IO [ClaimState.ClaimState claim]
runOnePathSteps
    breadthLimit
    depthLimit
    claim
    coinductiveRewrites
    rewrites =
        do
            result <-
                runSteps
                    breadthLimit
                    Just
                    pickFinal
                    coinductiveRewrites
                    (groupSortOn Attribute.Axiom.getPriorityOfAxiom rewrites)
                    claim
                    (Limit.takeWithin depthLimit (toList strategy))
            return (sort $ nub result)

assertStuck ::
    OnePathClaim ->
    [ClaimState.ClaimState OnePathClaim] ->
    [ClaimState.ClaimState SomeClaim] ->
    IO ()
assertStuck expectedGoal actual actualReach = do
    assertEqual "as one-path claim" [Stuck expectedGoal] actual
    assertEqual "as reachability claim" (asOnePath actual) actualReach
  where
    asOnePath = (fmap . fmap) OnePath
