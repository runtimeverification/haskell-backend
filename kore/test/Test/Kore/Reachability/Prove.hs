module Test.Kore.Reachability.Prove
    ( test_reachabilityVerification
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Control.Lens as Lens
import Data.Default
    ( def
    )
import Data.Generics.Product
    ( field
    )
import Data.Limit
    ( Limit (..)
    )
import Numeric.Natural
    ( Natural
    )

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate_
    )
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , mkRuleVariable
    )
import Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    )
import Kore.Step.RulePattern
    ( RulePattern (..)
    , injectTermIntoRHS
    , mkRewritingRule
    , rulePattern
    )
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import Kore.Unparser
    ( unparseToText2
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_reachabilityVerification :: [TestTree]
test_reachabilityVerification =
    [ testCase "OnePath: Runs zero steps" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            (Limit 0)
            [simpleAxiom Mock.a Mock.b]
            [simpleOnePathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "AllPath: Runs zero steps" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            (Limit 0)
            [simpleAxiom Mock.a Mock.b]
            [simpleAllPathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "Mixed: Runs zero steps" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            (Limit 0)
            [simpleAxiom Mock.a Mock.b]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "OnePath: Breadth limit zero" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            (Limit 0)
            Unlimited
            [simpleAxiom Mock.a Mock.b]
            [simpleOnePathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "AllPath: Breadth limit zero" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            (Limit 0)
            Unlimited
            [simpleAxiom Mock.a Mock.b]
            [simpleAllPathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "Mixed: Breadth limit zero" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            (Limit 0)
            Unlimited
            [simpleAxiom Mock.a Mock.b]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "OnePath: Runs one step" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error b
        -- Note that the check that we have reached the destination happens
        -- at the beginning of each step. At the beginning of the first step
        -- the pattern is 'a', so we didn't reach our destination yet, even if
        -- the rewrite transforms 'a' into 'b'. We detect the success at the
        -- beginning of the second step, which does not run here.
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            [simpleAxiom Mock.a Mock.b]
            [simpleOnePathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "AllPath: Runs one step" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error b
        -- Note that the check that we have reached the destination happens
        -- at the beginning of each step. At the beginning of the first step
        -- the pattern is 'a', so we didn't reach our destination yet, even if
        -- the rewrite transforms 'a' into 'b'. We detect the success at the
        -- beginning of the second step, which does not run here.
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            [simpleAxiom Mock.a Mock.b]
            [simpleAllPathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "Mixed: Runs one step" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error b
        -- Note that the check that we have reached the destination happens
        -- at the beginning of each step. At the beginning of the first step
        -- the pattern is 'a', so we didn't reach our destination yet, even if
        -- the rewrite transforms 'a' into 'b'. We detect the success at the
        -- beginning of the second step, which does not run here.
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            [simpleAxiom Mock.a Mock.b]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "OnePath: Identity spec" $ do
        -- Axioms: []
        -- Claims: a => a
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            []
            [ simpleOnePathClaim Mock.a Mock.a ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Identity spec" $ do
        -- Axioms: []
        -- Claims: a => a
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            []
            [ simpleAllPathClaim Mock.a Mock.a ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Identity spec" $ do
        -- Axioms: []
        -- Claims: a => a
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            []
            [ simpleOnePathClaim Mock.a Mock.a
            , simpleAllPathClaim Mock.a Mock.a
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Distinct spec" $ do
        -- Axioms: []
        -- Claims: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            Unlimited
            []
            [ simpleOnePathClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "AllPath: Distinct spec" $ do
        -- Axioms: []
        -- Claims: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            Unlimited
            []
            [ simpleAllPathClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "Mixed: Distinct spec" $ do
        -- Axioms: []
        -- Claims: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            Unlimited
            []
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "OnePath: b or c spec" $ do
        -- Axioms: a => b
        -- Claims: a => b #Or c
        -- Expected: success
        actual <- proveClaims_
            (Limit 2)
            Unlimited
            [ simpleAxiom Mock.a Mock.b ]
            [ simpleOnePathClaim Mock.a (mkOr Mock.b Mock.c) ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: b or c spec" $ do
        -- Axioms: a => b
        -- Claims: a => b #Or c
        -- Expected: success
        actual <- proveClaims_
            (Limit 2)
            Unlimited
            [ simpleAxiom Mock.a Mock.b ]
            [ simpleAllPathClaim Mock.a (mkOr Mock.b Mock.c) ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: b or c spec" $ do
        -- Axioms: a => b
        -- Claims: a => b #Or c
        -- Expected: success
        actual <- proveClaims_
            (Limit 2)
            Unlimited
            [ simpleAxiom Mock.a Mock.b ]
            [ simpleAllPathClaim Mock.a (mkOr Mock.b Mock.c)
            , simpleAllPathClaim Mock.a (mkOr Mock.b Mock.c)
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Everything is provable when we have cyclic rules" $ do
        -- Axioms: a => a
        -- Claims: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.a ]
            [ simpleOnePathClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Everything is provable when we have cyclic rules" $ do
        -- Axioms: a => a
        -- Claims: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.a ]
            [ simpleAllPathClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Everything is provable when we have cyclic rules" $ do
        -- Axioms: a => a
        -- Claims: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.a ]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Concurrent rules" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claims: a => b #Or c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 2)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleOnePathClaim Mock.a (mkOr Mock.b Mock.c) ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Concurrent rules" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claims: a => b #Or c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 2)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleAllPathClaim Mock.a (mkOr Mock.b Mock.c) ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Concurrent rules" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claims: a => b #Or c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 2)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleOnePathClaim Mock.a (mkOr Mock.b Mock.c)
            , simpleOnePathClaim Mock.a (mkOr Mock.b Mock.c)
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Returns first failing claim" $ do
        -- Axiom: a => b or c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            [simpleAxiom Mock.a (mkOr Mock.b Mock.c)]
            [simpleOnePathClaim Mock.a Mock.d]
            []
        assertEqual ""
            (Left . OrPattern.fromTermLike $ Mock.b)
            actual
    , testCase "AllPath: Returns first failing claim" $ do
        -- Axiom: a => b or c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            [simpleAxiom Mock.a (mkOr Mock.b Mock.c)]
            [simpleAllPathClaim Mock.a Mock.d]
            []
        assertEqual ""
            (Left . OrPattern.fromTermLike $ Mock.b)
            actual
    , testCase "Mixed: Returns first failing claim" $ do
        -- Axiom: a => b or c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 1)
            [simpleAxiom Mock.a (mkOr Mock.b Mock.c)]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left . OrPattern.fromTermLike $ Mock.b)
            actual
    , testCase "OnePath: Verifies one claim" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 2)
            [simpleAxiom Mock.a Mock.b]
            [simpleOnePathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Verifies one claim" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 2)
            [simpleAxiom Mock.a Mock.b]
            [simpleAllPathClaim Mock.a Mock.b]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Verifies one claim" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 2)
            [simpleAxiom Mock.a Mock.b]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Trusted claim cannot prove itself" $ do
        -- Trusted Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            []
            [ simpleOnePathTrustedClaim Mock.a Mock.b
            , simpleOnePathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "AllPath: Trusted claim cannot prove itself" $ do
        -- Trusted Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            []
            [ simpleAllPathTrustedClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "Mixed: Trusted claim cannot prove itself" $ do
        -- Trusted Claim: a => b
        -- Expected: error a
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            []
            [ simpleOnePathTrustedClaim Mock.a Mock.b
            , simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathTrustedClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.a)
            actual
    , testCase "OnePath: Verifies one claim multiple steps" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [simpleOnePathClaim Mock.a Mock.c]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Verifies one claim multiple steps" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [simpleAllPathClaim Mock.a Mock.c]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Verifies one claim multiple steps" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [ simpleOnePathClaim Mock.a Mock.c
            , simpleAllPathClaim Mock.a Mock.c
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Verifies one claim stops early" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [simpleOnePathClaim Mock.a Mock.c]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Verifies one claim stops early" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [simpleAllPathClaim Mock.a Mock.c]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Verifies one claim stops early" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [ simpleOnePathClaim Mock.a Mock.c
            , simpleAllPathClaim Mock.a Mock.c
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: Verifies one claim with branching" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr11(x) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom (Mock.functionalConstr11 (mkElemVar Mock.x)) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleOnePathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual "" (Right ()) actual
    , testCase "AllPath: Verifies one claim with branching" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr11(x) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom (Mock.functionalConstr11 (mkElemVar Mock.x)) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleAllPathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual "" (Right ()) actual
    , testCase "Mixed: Verifies one claim with branching" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr11(x) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom (Mock.functionalConstr11 (mkElemVar Mock.x)) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleOnePathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            , simpleAllPathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual "" (Right ()) actual
    , testCase "OnePath: Partial verification failure" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleOnePathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual ""
            ( Left . OrPattern.fromPattern
            $ Conditional
                { term = Mock.functionalConstr11 (mkElemVar Mock.x)
                , predicate =
                    makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                , substitution = mempty
                }
            )
            actual
    , testCase "AllPath: Partial verification failure" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleAllPathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual ""
            ( Left . OrPattern.fromPattern
            $ Conditional
                { term = Mock.functionalConstr11 (mkElemVar Mock.x)
                , predicate =
                    makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                , substitution = mempty
                }
            )
            actual
    , testCase "Mixed: Partial verification failure" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleOnePathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            , simpleAllPathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual ""
            ( Left . OrPattern.fromPattern
            $ Conditional
                { term = Mock.functionalConstr11 (mkElemVar Mock.x)
                , predicate =
                    makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                , substitution = mempty
                }
            )
            actual
    , testCase "OnePath: Stops at branching because of breadth limit" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- proveClaims_
            (Limit 1)
            Unlimited
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleOnePathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual ""
            ( Left . OrPattern.fromPatterns $
            [ Pattern.withCondition
                (Mock.functionalConstr11 (mkElemVar Mock.x))
                (Condition.fromPredicate
                    (makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                    )
                )
            , Pattern.withCondition
                Mock.b
                (Condition.assign (inject Mock.x) Mock.a)
            ]
            )
            actual
    , testCase "AllPath: Stops at branching because of breadth limit" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- proveClaims_
            (Limit 1)
            Unlimited
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleAllPathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual ""
            ( Left . OrPattern.fromPatterns $
            [ Pattern.withCondition
                (Mock.functionalConstr11 (mkElemVar Mock.x))
                (Condition.fromPredicate
                    (makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                    )
                )
            , Pattern.withCondition
                Mock.b
                (Condition.assign (inject Mock.x) Mock.a)
            ]
            )
            actual
    , testCase "Mixed: Stops at branching because of breadth limit" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- proveClaims_
            (Limit 1)
            Unlimited
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [ simpleOnePathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            , simpleAllPathClaim
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                Mock.b
            ]
            []
        assertEqual ""
            ( Left . OrPattern.fromPatterns $
            [ Pattern.withCondition
                (Mock.functionalConstr11 (mkElemVar Mock.x))
                (Condition.fromPredicate
                    (makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                    )
                )
            , Pattern.withCondition
                Mock.b
                (Condition.assign (inject Mock.x) Mock.a)
            ]
            )
            actual
    , testCase "OnePath: Verifies two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => e
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.c
            , simpleOnePathClaim Mock.d Mock.e
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Verifies two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => e
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleAllPathClaim Mock.a Mock.c
            , simpleAllPathClaim Mock.d Mock.e
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: Verifies two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => e
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleAllPathClaim Mock.a Mock.c
            , simpleOnePathClaim Mock.d Mock.e
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: fails first of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => e
        -- Claim: d => e
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.e
            , simpleOnePathClaim Mock.d Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "AllPath: fails first of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => e
        -- Claim: d => e
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleAllPathClaim Mock.a Mock.e
            , simpleAllPathClaim Mock.d Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "Mixed: fails first of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => e
        -- Claim: d => e
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.e
            , simpleAllPathClaim Mock.d Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "OnePath: fails second of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => c
        -- Expected: error e
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.c
            , simpleOnePathClaim Mock.d Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.e)
            actual
    , testCase "AllPath: fails second of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => c
        -- Expected: error e
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleAllPathClaim Mock.a Mock.c
            , simpleAllPathClaim Mock.d Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.e)
            actual
    , testCase "Mixed: fails second of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => c
        -- Expected: error e
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.c
            , simpleAllPathClaim Mock.d Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.e)
            actual
    , testCase "OnePath: skips proven claim" $ do
        -- Axiom: d => e
        -- Claim: a => b
        -- Claim: d => e
        -- Already proven: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleOnePathClaim Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.b
            ]
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: skips proven claim" $ do
        -- Axiom: d => e
        -- Claim: a => b
        -- Claim: d => e
        -- Already proven: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.d Mock.e
            ]
            [ simpleAllPathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.d Mock.e
            ]
            [ simpleAllPathClaim Mock.a Mock.b
            ]
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: skips proven claim" $ do
        -- Axiom: d => e
        -- Claim: a => b
        -- Claim: d => e
        -- Already proven: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.d Mock.e
            ]
            [ simpleOnePathClaim Mock.a Mock.b
            ]
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath: second proves first but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => c
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleOnePathClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "AllPath: second proves first but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => c
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleAllPathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "Mixed: second proves first but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => c
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleOnePathClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "Mixed: different claim types so\
               \ second can't prove first" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => c
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "OnePath: first proves second but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.b Mock.c
            , simpleOnePathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "AllPath: first proves second but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleAllPathClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "Mixed: first proves second but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.b Mock.c
            , simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "Mixed: first doesn't prove second\
               \ because they are different claim types" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "OnePath: trusted second proves first" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Trusted Claim: b => c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleOnePathTrustedClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: trusted second proves first" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Trusted Claim: b => c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleAllPathClaim Mock.a Mock.d
            , simpleAllPathTrustedClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: trusted second proves first" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Trusted Claim: b => c
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleOnePathTrustedClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            , simpleAllPathTrustedClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: trusted second doesn't prove first\
               \ because of different claim types" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Trusted Claim: b => c
        -- Expected: error b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathTrustedClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "OnePath: trusted first proves second" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathTrustedClaim Mock.b Mock.c
            , simpleOnePathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: trusted first proves second" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleAllPathTrustedClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed: trusted first doesn't proves second\
                \ because they are different claim types" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathTrustedClaim Mock.b Mock.c
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.b)
            actual
    , testCase "OnePath: Prefers using claims for rewriting" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => e
        -- Expected: error e
        --    first verification: a=>b=>e,
        --        without second claim would be: a=>b=>c=>d
        --    second verification: b=>c=>d, not visible here
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleOnePathClaim Mock.b Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.e)
            actual
    , testCase "AllPath: Prefers using claims for rewriting" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => e
        -- Expected: error e
        --    first verification: a=>b=>e,
        --        without second claim would be: a=>b=>c=>d
        --    second verification: b=>c=>d, not visible here
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleAllPathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.e)
            actual
    , testCase "Mixed: Prefers using claims for rewriting" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => e
        -- Expected: error e
        --    first verification: a=>b=>e,
        --        without second claim would be: a=>b=>c=>d
        --    second verification: b=>c=>d, not visible here
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleOnePathClaim Mock.b Mock.e
            , simpleAllPathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.e)
            actual
    , testCase "Mixed: Doesn't apply claim because of\
               \ different claim type" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => e
        -- Expected: error d
        --    first verification: a=>b=>c=>d
        --    second verification: b=>c=>d is now visible here
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.b Mock.e
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.d)
            actual
    , testCase "OnePath: Provable using one-path; not provable\
               \ using all-path" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claim: a => b
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            (Limit 5)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleOnePathClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath: Provable using one-path; not provable\
               \ using all-path" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claim: a => b
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            (Limit 5)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleAllPathClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "Mixed: Provable using one-path; not provable\
               \ using all-path" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claim: a => b
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            (Limit 5)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleOnePathClaim Mock.a Mock.b
            , simpleAllPathClaim Mock.a Mock.b
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "OnePath Priority: can get stuck by choosing second axiom" $ do
        -- Axioms:
        --     a => b
        --     b => c
        --     b => d
        -- Claims: a => d
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.b Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "AllPath Priority: can get stuck by choosing second axiom" $ do
        -- Axioms:
        --     a => b
        --     b => c
        --     b => d
        -- Claims: a => d
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.b Mock.d
            ]
            [ simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "Mixed Priority: can get stuck by choosing second axiom" $ do
        -- Axioms:
        --     a => b
        --     b => c
        --     b => d
        -- Claims: a => d
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.b Mock.d
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "OnePath Priority: should succeed, prefering axiom with priority 1" $ do
        -- Axioms:
        --     a => b
        --     b => c [priority(2)]
        --     b => d [priority(1)]
        -- Claims: a => d
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simplePriorityAxiom Mock.b Mock.c 2
            , simplePriorityAxiom Mock.b Mock.d 1
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "AllPath Priority: should succeed, prefering axiom with priority 1" $ do
        -- Axioms:
        --     a => b
        --     b => c [priority(2)]
        --     b => d [priority(1)]
        -- Claims: a => d
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simplePriorityAxiom Mock.b Mock.c 2
            , simplePriorityAxiom Mock.b Mock.d 1
            ]
            [ simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Mixed Priority: should succeed, prefering axiom with priority 1" $ do
        -- Axioms:
        --     a => b
        --     b => c [priority(2)]
        --     b => d [priority(1)]
        -- Claims: a => d
        -- Expected: success
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simplePriorityAxiom Mock.b Mock.c 2
            , simplePriorityAxiom Mock.b Mock.d 1
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "OnePath Priority: should fail, prefering axiom with priority 1" $ do
        -- Axioms:
        --     a => b
        --     b => c [priority(2)]
        --     b => d [priority(1)]
        -- Claims: a => d
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simplePriorityAxiom Mock.b Mock.d 2
            , simplePriorityAxiom Mock.b Mock.c 1
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "AllPath Priority: should fail, prefering axiom with priority 1" $ do
        -- Axioms:
        --     a => b
        --     b => c [priority(2)]
        --     b => d [priority(1)]
        -- Claims: a => d
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simplePriorityAxiom Mock.b Mock.d 2
            , simplePriorityAxiom Mock.b Mock.c 1
            ]
            [ simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    , testCase "Mixed Priority: should fail, prefering axiom with priority 1" $ do
        -- Axioms:
        --     a => b
        --     b => c [priority(2)]
        --     b => d [priority(1)]
        -- Claims: a => d
        -- Expected: error c
        actual <- proveClaims_
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b
            , simplePriorityAxiom Mock.b Mock.d 2
            , simplePriorityAxiom Mock.b Mock.c 1
            ]
            [ simpleOnePathClaim Mock.a Mock.d
            , simpleAllPathClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ OrPattern.fromTermLike Mock.c)
            actual
    ]

simpleAxiom
    :: TermLike VariableName
    -> TermLike VariableName
    -> Rule SomeClaim
simpleAxiom left right =
    ReachabilityRewriteRule $ simpleRewrite left right

simpleClaim
    :: TermLike VariableName
    -> TermLike VariableName
    -> ClaimPattern
simpleClaim
    (TermLike.mapVariables (pure mkRuleVariable) -> left)
    (TermLike.mapVariables (pure mkRuleVariable) -> right)
  =
    ClaimPattern
            { left =
                Pattern.fromTermAndPredicate
                    left
                    (makeTruePredicate (termLikeSort left))
            , right =
                Pattern.fromTermAndPredicate
                    right
                    (makeTruePredicate (termLikeSort right))
                & OrPattern.fromPattern
            , existentials = []
            , attributes = def
            }

simpleOnePathClaim
    :: TermLike VariableName
    -> TermLike VariableName
    -> SomeClaim
simpleOnePathClaim left right =
    OnePath . OnePathClaim $ simpleClaim left right

simpleAllPathClaim
    :: TermLike VariableName
    -> TermLike VariableName
    -> SomeClaim
simpleAllPathClaim left right =
    AllPath . AllPathClaim $ simpleClaim left right

simpleOnePathTrustedClaim
    :: TermLike VariableName
    -> TermLike VariableName
    -> SomeClaim
simpleOnePathTrustedClaim left right =
    Lens.set
        (lensClaimPattern . field @"attributes" . field @"trusted")
        (Attribute.Trusted True)
    . OnePath
    . OnePathClaim
    $ simpleClaim left right

simpleAllPathTrustedClaim
    :: TermLike VariableName
    -> TermLike VariableName
    -> SomeClaim
simpleAllPathTrustedClaim left right =
    Lens.set
        (lensClaimPattern . field @"attributes" . field @"trusted")
        (Attribute.Trusted True)
    . AllPath
    . AllPathClaim
    $ simpleClaim left right

simplePriorityAxiom
    :: TermLike VariableName
    -> TermLike VariableName
    -> Integer
    -> Rule SomeClaim
simplePriorityAxiom left right priority =
    ReachabilityRewriteRule . mkRewritingRule . RewriteRule
    $ RulePattern
        { left = left
        , antiLeft = Nothing
        , requires = makeTruePredicate_
        , rhs = injectTermIntoRHS right
        , attributes = def
            { Attribute.priority = Attribute.Priority (Just priority)
            }
        }


simpleRewrite
    :: TermLike VariableName
    -> TermLike VariableName
    -> RewriteRule RewritingVariableName
simpleRewrite left right =
    mkRewritingRule $ RewriteRule $ rulePattern left right

proveClaims
    :: Limit Natural
    -> Limit Natural
    -> [Rule SomeClaim]
    -> [SomeClaim]
    -> [SomeClaim]
    -> IO ProveClaimsResult
proveClaims breadthLimit depthLimit axioms claims alreadyProven =
    Kore.Reachability.proveClaims
        breadthLimit
        BreadthFirst
        (AllClaims claims)
        (Axioms axioms)
        (AlreadyProven (map unparseToText2 alreadyProven))
        (ToProve (map applyDepthLimit . selectUntrusted $ claims))
    & runSimplifier mockEnv
  where
    mockEnv = Mock.env
    applyDepthLimit claim = (claim, depthLimit)
    selectUntrusted = filter (not . isTrusted)

proveClaims_
    :: Limit Natural
    -> Limit Natural
    -> [Rule SomeClaim]
    -> [SomeClaim]
    -> [SomeClaim]
    -> IO (Either (OrPattern VariableName) ())
proveClaims_ breadthLimit depthLimit axioms claims alreadyProven =
    do
        ProveClaimsResult { stuckClaim } <-
            Test.Kore.Reachability.Prove.proveClaims
                breadthLimit
                depthLimit
                axioms
                claims
                alreadyProven
        pure $ maybe (Right ()) (Left . getStuckClaim) stuckClaim
