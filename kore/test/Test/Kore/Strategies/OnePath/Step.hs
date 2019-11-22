module Test.Kore.Strategies.OnePath.Step
    ( test_onePathStrategy
    ) where

import Test.Tasty

import Data.Coerce
    ( coerce
    )
import Data.Default
    ( def
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import Data.List
    ( nub
    , sort
    )
import Data.Maybe
    ( fromMaybe
    )
import Data.Reflection
    ( give
    )
import Numeric.Natural
    ( Natural
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit

import Kore.IndexedModule.IndexedModule
    ( indexedModuleWithDefaultImports
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeEqualsPredicate_
    , makeMultipleAndPredicate
    , makeNotPredicate
    , makeTruePredicate_
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Rule
    ( OnePathRule (..)
    , ReachabilityRule (..)
    , RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    , rulePattern
    )
import Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    )
import Kore.Step.SMT.Lemma
    ( declareSMTLemmas
    )
import Kore.Step.Strategy
    ( ExecutionGraph (..)
    , Strategy
    , pickFinal
    , runStrategy
    )
import Kore.Strategies.Goal
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Syntax.Module
    ( ModuleName (ModuleName)
    )
import Kore.Syntax.Variable
    ( Variable (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext


makeOnePathRule
    :: TermLike Variable
    -> TermLike Variable
    -> OnePathRule Variable
makeOnePathRule term dest =
    OnePathRule $ rulePattern term dest

makeOnePathRuleFromPatterns
    :: Pattern Variable
    -> Pattern Variable
    -> OnePathRule Variable
makeOnePathRuleFromPatterns
    configuration
    destination
  =
    let (left, Condition.toPredicate -> requires) =
            Pattern.splitTerm configuration
        (right, Condition.toPredicate -> ensures) =
            Pattern.splitTerm destination
    in coerce RulePattern
        { left
        , antiLeft = Nothing
        , right
        , requires
        , ensures
        , attributes = Default.def
        }

makeReachabilityOnePathRule
    :: TermLike Variable
    -> TermLike Variable
    -> ReachabilityRule Variable
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
            (Limit 0)
            (makeOnePathRule
                Mock.a
                Mock.a
            )
            [makeOnePathRule Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        [ actualReach ] <- runOnePathSteps
            (Limit 0)
            (makeReachabilityOnePathRule
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
            (Limit 1)
            (makeOnePathRule Mock.a Mock.a)
            [makeOnePathRule Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        [ _actualReach ] <- runOnePathSteps
            (Limit 1)
            (makeReachabilityOnePathRule Mock.a Mock.a)
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
            (Limit 1)
            (makeOnePathRule Mock.a Mock.d)
            [makeOnePathRule Mock.a Mock.b]
            [simpleRewrite Mock.a Mock.c]
        [ _actualReach ] <- runOnePathSteps
            (Limit 1)
            (makeReachabilityOnePathRule Mock.a Mock.d)
            [makeReachabilityOnePathRule Mock.a Mock.b]
            [simpleReachabilityRewrite Mock.a Mock.c]
        assertEqual ""
            (ProofState.Goal $ makeOnePathRule Mock.c Mock.d)
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
            (Limit 2)
            (makeOnePathRule
                Mock.a
                Mock.b
            )
            [makeOnePathRule Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        [ _actualReach ] <- runOnePathSteps
            (Limit 2)
            (makeReachabilityOnePathRule
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
            (Limit 2)
            (makeOnePathRule Mock.a Mock.e)
            [makeOnePathRule Mock.b Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        [ _actual1Reach ] <- runOnePathSteps
            (Limit 2)
            (makeReachabilityOnePathRule Mock.a Mock.e)
            [makeReachabilityOnePathRule Mock.b Mock.c]
            [ simpleReachabilityRewrite Mock.b Mock.d
            , simpleReachabilityRewrite Mock.a Mock.b
            ]
        assertEqual ""
            (sort
                [ ProofState.Goal $ makeOnePathRule Mock.c Mock.e
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
            (Limit 2)
            (makeOnePathRule Mock.a Mock.e)
            [makeOnePathRule Mock.e Mock.c]
            [ simpleRewrite Mock.b Mock.d
            , simpleRewrite Mock.a Mock.b
            ]
        [ _actualReach ] <- runOnePathSteps
            (Limit 2)
            (makeReachabilityOnePathRule Mock.a Mock.e)
            [makeReachabilityOnePathRule Mock.e Mock.c]
            [ simpleReachabilityRewrite Mock.b Mock.d
            , simpleReachabilityRewrite Mock.a Mock.b
            ]
        assertEqual ""
            (sort
                [ ProofState.Goal $ makeOnePathRule Mock.d Mock.e
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
                (Limit 2)
                (makeReachabilityOnePathRule
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
        let expected =
                [ ProofState.Goal $ makeOnePathRuleFromPatterns
                    ( Conditional
                        { term = Mock.f Mock.b
                        , predicate = makeTruePredicate_
                        , substitution =
                            Substitution.unsafeWrap
                                [(ElemVar Mock.x, Mock.b)]
                        }
                    )
                    (fromTermLike $ Mock.functionalConstr11 Mock.a)
                , ProofState.Goal $ makeOnePathRuleFromPatterns
                    ( Conditional
                        { term = Mock.f Mock.c
                        , predicate = makeTruePredicate_
                        , substitution =
                            Substitution.unsafeWrap
                                [(ElemVar Mock.x, Mock.c)]
                        }
                    )
                    (fromTermLike $ Mock.functionalConstr11 Mock.a)
                , ProofState.Goal $ makeOnePathRuleFromPatterns
                    ( Conditional
                        { term = Mock.h (TermLike.mkElemVar Mock.x)
                        , predicate =  -- TODO(virgil): Better and simplification.
                            makeAndPredicate
                                (makeAndPredicate
                                    (makeNotPredicate
                                        (makeEqualsPredicate_
                                            (TermLike.mkElemVar Mock.x) Mock.a
                                        )
                                    )
                                    (makeNotPredicate
                                        (makeEqualsPredicate_
                                            (TermLike.mkElemVar Mock.x) Mock.b
                                        )
                                    )
                                )
                                (makeNotPredicate
                                    (makeEqualsPredicate_
                                        (TermLike.mkElemVar Mock.x)
                                        Mock.c
                                    )
                                )
                        , substitution = mempty
                        }
                    )
                    (fromTermLike $ Mock.functionalConstr11 Mock.a)
                ]
        assertEqual ""
            expected
            actual
        assertEqual "onepath == reachability onepath"
            (fmap (fmap OnePath) actual)
            actualReach
    , testCase "Stuck pattern" $ do
        -- Goal: constr10(x) => constr11(a)
        -- Coinductive axiom: constr11(b) => f(b)
        -- Normal axiom: constr11(c) => f(c)
        -- Normal axiom: constr10(x) => constr11(x)
        -- Expected:
        --   Bottom
        --   or (f(b) and x=b)
        --   or (f(c) and x=c)
        --   Stuck (functionalConstr11(x) and x!=a and x!=b and x!=c )
        actual@[ _actual1, _actual2, _actual3 ] <-
            runOnePathSteps
                (Limit 2)
                (makeOnePathRule
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
                (Limit 2)
                (makeReachabilityOnePathRule
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
        let equalsXA = makeEqualsPredicate_ (TermLike.mkElemVar Mock.x) Mock.a
            equalsXB = makeEqualsPredicate_ (TermLike.mkElemVar Mock.x) Mock.b
            equalsXC = makeEqualsPredicate_ (TermLike.mkElemVar Mock.x) Mock.c
        assertEqual ""
            [ ProofState.Goal $ makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.f Mock.b
                    , predicate = makeTruePredicate_
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.b)]
                    }
                )
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
            , ProofState.Goal $ makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.f Mock.c
                    , predicate = makeTruePredicate_
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.c)]
                    }
                )
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
            , ProofState.GoalRemainder $ makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr11 (TermLike.mkElemVar Mock.x)
                    , predicate =
                        makeMultipleAndPredicate
                            [ makeNotPredicate equalsXA
                            , makeNotPredicate equalsXB
                            , makeNotPredicate equalsXC
                            ]
                    , substitution = mempty
                    }
                )
                (fromTermLike $ Mock.functionalConstr11 Mock.a)
            ]
            [ _actual1
            , _actual2
            , _actual3
            ]
        assertEqual "onepath == reachability onepath"
            (fmap (fmap OnePath) actual)
            actualReach
    , testCase "Axiom with requires" $ do
        -- Goal:  constr10(b) => a
        -- Coinductive axiom: n/a
        -- Normal axiom: constr10(b) => a | f(b) == c
        -- Expected: a | f(b) == c
        actual@[ _actual1, _actual2 ] <- runOnePathSteps
            (Limit 2)
            (makeOnePathRule
                (Mock.functionalConstr10 Mock.b)
                Mock.a
            )
            []
            [ rewriteWithPredicate
                (Mock.functionalConstr10 Mock.b)
                Mock.a
                $ makeEqualsPredicate_
                    Mock.c
                    $ Mock.f Mock.b
            ]
        actualReach <- runOnePathSteps
            (Limit 2)
            (makeReachabilityOnePathRule
                (Mock.functionalConstr10 Mock.b)
                Mock.a
            )
            []
            [ rewriteReachabilityWithPredicate
                (Mock.functionalConstr10 Mock.b)
                Mock.a
                $ makeEqualsPredicate_
                    Mock.c
                    $ Mock.f Mock.b
            ]
        assertEqual ""
            [ ProofState.GoalRemainder
            $ makeOnePathRuleFromPatterns
                ( Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate =
                        makeNotPredicate
                            $ makeEqualsPredicate_
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
        assertEqual "onepath == reachability onepath"
            (fmap (fmap OnePath) actual)
            actualReach
    , testCase "Stuck pattern simplification" $ do
        -- Goal: 0 => 1
        -- Coinductive axioms: none
        -- Normal axiom: x => 1 if x<2
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
                    (makeEqualsPredicate_
                        (Mock.lessInt
                            (TermLike.mkElemVar Mock.xInt) (Mock.builtinInt 2)
                        )
                        (Mock.builtinBool True)
                    )
                ]
        [ _actualReach ] <-
            runOnePathSteps
                (Limit 2)
                ( makeReachabilityOnePathRule
                    (Mock.builtinInt 0)
                    (Mock.builtinInt 1)
                )
                []
                [ rewriteReachabilityWithPredicate
                    (TermLike.mkElemVar Mock.xInt)
                    (Mock.builtinInt 1)
                    (makeEqualsPredicate_
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
            (Limit 1)
            (makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate = makeEqualsPredicate_
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
                (makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            , rewriteWithPredicate
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                Mock.c
                (makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool False)
                )
            ]
        [ _actualReach ] <- runOnePathSteps
            (Limit 1)
            (OnePath $ makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate = makeEqualsPredicate_
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
                (makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            , rewriteReachabilityWithPredicate
                (Mock.functionalConstr10 (TermLike.mkElemVar Mock.x))
                Mock.c
                (makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool False)
                )
            ]
        assertEqual ""
            [ ProofState.Goal $ makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.a
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.lessInt
                                (Mock.fTestInt Mock.b)
                                (Mock.builtinInt 0)
                            )
                            (Mock.builtinBool True)
                    , substitution = mempty
                    }
                )
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
            (Limit 1)
            (makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate = makeEqualsPredicate_
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
                (makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            ]
        [ _actualReach ] <- runOnePathSteps
            (Limit 1)
            (OnePath $ makeOnePathRuleFromPatterns
                (Conditional
                    { term = Mock.functionalConstr10 Mock.b
                    , predicate = makeEqualsPredicate_
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
                (makeEqualsPredicate_
                    (Mock.lessInt
                        (Mock.fTestInt (TermLike.mkElemVar Mock.x))
                        (Mock.builtinInt 0)
                    )
                    (Mock.builtinBool True)
                )
            ]
        assertEqual ""
            [ ProofState.Goal $ makeOnePathRuleFromPatterns
                ( Conditional
                    { term = Mock.a
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.lessInt
                                (Mock.fTestInt Mock.b)
                                (Mock.builtinInt 0)
                            )
                            (Mock.builtinBool True)
                    , substitution = mempty
                    }
                )
                (fromTermLike Mock.a)
            ]
            [ _actual ]
        assertEqual "onepath == reachability onepath"
            (fmap OnePath _actual)
            _actualReach
    ]

simpleRewrite
    :: TermLike Variable
    -> TermLike Variable
    -> Rule (OnePathRule Variable)
simpleRewrite left right =
    OnePathRewriteRule
    $ RewriteRule RulePattern
        { left = left
        , antiLeft = Nothing
        , right = right
        , requires = makeTruePredicate_
        , ensures = makeTruePredicate_
        , attributes = def
        }

simpleReachabilityRewrite
    :: TermLike Variable
    -> TermLike Variable
    -> Rule (ReachabilityRule Variable)
simpleReachabilityRewrite left right =
    coerce (simpleRewrite left right)

rewriteWithPredicate
    :: TermLike Variable
    -> TermLike Variable
    -> Predicate Variable
    -> Rule (OnePathRule Variable)
rewriteWithPredicate left right predicate =
    OnePathRewriteRule
    $ RewriteRule RulePattern
        { left = left
        , antiLeft = Nothing
        , right = right
        , requires = predicate
        , ensures = makeTruePredicate_
        , attributes = def
        }

rewriteReachabilityWithPredicate
    :: TermLike Variable
    -> TermLike Variable
    -> Predicate Variable
    -> Rule (ReachabilityRule Variable)
rewriteReachabilityWithPredicate left right predicate =
    coerce (rewriteWithPredicate left right predicate)

runSteps
    :: Goal goal
    => ProofState goal goal ~ ProofState.ProofState goal
    => ( ExecutionGraph
            (ProofState goal goal)
            (Rule goal)
       -> Maybe (ExecutionGraph b c)
       )
    -> (ExecutionGraph b c -> a)
    -> goal
    -- ^left-hand-side of unification
    -> [Strategy (Prim goal)]
    -> IO a
runSteps graphFilter picker configuration strategy' =
    (<$>) picker
    $ runSimplifier mockEnv
    $ fromMaybe (error "Unexpected missing tree") . graphFilter
    <$> do
        give metadataTools
            $ declareSMTLemmas
            $ indexedModuleWithDefaultImports (ModuleName "TestModule") Nothing
        runStrategy transitionRule strategy' (ProofState.Goal configuration)
  where
    mockEnv = Mock.env
    Env {metadataTools} = mockEnv

runOnePathSteps
    :: Goal goal
    => ProofState goal goal ~ ProofState.ProofState goal
    => Ord goal
    => Limit Natural
    -> goal
    -- ^left-hand-side of unification
    -> [goal]
    -> [Rule goal]
    -> IO [ProofState goal goal]
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
            (Foldable.toList $ strategy goal coinductiveRewrites rewrites)
        )
    return (sort $ nub result)
