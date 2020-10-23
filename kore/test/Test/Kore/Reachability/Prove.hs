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
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
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
    , mkRewritingPattern
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
    [ testGroup "runs zero steps with depth = 0" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <- proveClaims_
                        Unlimited
                        (Limit 0)
                        [simpleAxiom Mock.a Mock.b]
                        [claim]
                        []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
    , testGroup "runs zero steps with breadth = 0" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <- proveClaims_
                        (Limit 0)
                        Unlimited
                        [simpleAxiom Mock.a Mock.b]
                        [claim]
                        []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
    , testGroup "runs one step with depth = 1" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <- proveClaims_
                        Unlimited
                        (Limit 1)
                        [simpleAxiom Mock.a Mock.b]
                        [claim]
                        []
                    -- Note that the check that we have reached the destination
                    -- happens at the beginning of each step. At the beginning
                    -- of the first step the pattern is 'a', so we didn't reach
                    -- our destination yet, even if the rewrite transforms 'a'
                    -- into 'b'. We detect the success at the beginning of the
                    -- second step, which does not run here.
                    let stuck = mkSimpleClaim Mock.b Mock.b
                        expect = MultiAnd.singleton (StuckClaim stuck)
                    assertEqual "" expect actual
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
    , testGroup "proves direct implication" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <- proveClaims_
                        Unlimited
                        (Limit 1)
                        []
                        [mkSimpleClaim Mock.a Mock.a]
                        []
                    assertEqual "" MultiAnd.top actual
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
    , testGroup "does not prove implication without rewriting" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <- proveClaims_
                        Unlimited
                        Unlimited
                        []
                        [claim]
                        []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
    , testGroup "proves by rewriting into disjunction" $
        let mkTest name mkSomeClaim =
                testCase name $ do
                    actual <- proveClaims_
                        (Limit 2)
                        Unlimited
                        [ simpleAxiom Mock.a Mock.b ]
                        [ mkSomeClaim
                            (Pattern.fromTermLike Mock.a)
                            (OrPattern.fromPatterns $ map Pattern.fromTermLike
                                [ Mock.b
                                , Mock.c
                                ]
                            )
                            []
                        ]
                        []
                    assertEqual "" MultiAnd.top actual
        in
        [ mkTest "OnePath" mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath
        ]
    , testGroup "proves anything with cyclic rules" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <- proveClaims_
                        Unlimited
                        (Limit 3)
                        [ simpleAxiom Mock.a Mock.a ]
                        [ mkSimpleClaim Mock.a Mock.b ]
                        []
                    assertEqual "" MultiAnd.top actual
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        let stuck = simpleOnePathClaim Mock.b Mock.d
            expect = MultiAnd.singleton (StuckClaim stuck)
        assertEqual "" expect actual
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
        let stuck = simpleAllPathClaim Mock.b Mock.d
            expect = MultiAnd.singleton (StuckClaim stuck)
        assertEqual "" expect actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
    , testCase "OnePath: Trusted claim cannot prove itself" $ do
        -- Trusted Claim: a => b
        -- Expected: error a
        let claim = simpleOnePathClaim Mock.a Mock.b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            []
            [ simpleOnePathTrustedClaim Mock.a Mock.b
            , claim
            ]
            []
        let expect = MultiAnd.singleton (StuckClaim claim)
        assertEqual "" expect actual
    , testCase "AllPath: Trusted claim cannot prove itself" $ do
        -- Trusted Claim: a => b
        -- Expected: error a
        let claim = simpleAllPathClaim Mock.a Mock.b
        actual <- proveClaims_
            Unlimited
            (Limit 4)
            []
            [ simpleAllPathTrustedClaim Mock.a Mock.b
            , claim
            ]
            []
        let expect = MultiAnd.singleton (StuckClaim claim)
        assertEqual "" expect actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
    , testGroup "reports only failed branch of proof" $
        let stuckCondition =
                makeNotPredicate
                    (makeEqualsPredicate Mock.testSort
                        (mkElemVar Mock.x)
                        Mock.a
                    )
                & Condition.fromPredicate
            stuckConfig =
                Pattern.withCondition
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                    stuckCondition
                & mkRewritingPattern
            axioms =
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
                , simpleAxiom
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                ]
        in
        [ testCase "OnePath" $ do
            actual <- proveClaims_
                Unlimited
                (Limit 3)
                axioms
                [ simpleOnePathClaim
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    Mock.b
                ]
                []
            let stuck =
                    mkOnePathClaim
                        stuckConfig
                        (OrPattern.fromTermLike Mock.b)
                        []
                    & OnePath
                expect = MultiAnd.singleton (StuckClaim stuck)
            assertEqual "" expect actual
        , testCase "AllPath" $ do
            actual <- proveClaims_
                Unlimited
                (Limit 3)
                axioms
                [ simpleAllPathClaim
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    Mock.b
                ]
                []
            let stuck =
                    mkAllPathClaim
                        stuckConfig
                        (OrPattern.fromTermLike Mock.b)
                        []
                    & AllPath
                expect = MultiAnd.singleton (StuckClaim stuck)
            assertEqual "" expect actual
        ]
    , testGroup "stops when breadth limit is exceeded" $
        let axioms =
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
                , simpleAxiom
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                ]
            stuckConfigs =
                map mkRewritingPattern
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
            initialPattern =
                Pattern.fromTermLike
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                & mkRewritingPattern
            finalPatterns = OrPattern.fromTermLike Mock.b
            mkTest name mkSomeClaim =
                testCase name $ do
                    actual <- proveClaims_
                        (Limit 1)
                        Unlimited
                        axioms
                        [mkSomeClaim initialPattern finalPatterns []]
                        []
                    let stuckClaims =
                            map
                                (\left -> mkSomeClaim left finalPatterns [])
                                stuckConfigs
                        expect = MultiAnd.make (StuckClaim <$> stuckClaims)
                    assertEqual "" expect actual
        in
        [ mkTest "OnePath" mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath
        ]
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
    , testGroup "does not prove first of two claims" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.b Mock.c
                , simpleAxiom Mock.d Mock.e
                ]
            right = OrPattern.fromTermLike Mock.e
            mkTest name mkSomeClaim1 mkSomeClaim2 =
                testCase name $ do
                    actual <- proveClaims_ Unlimited (Limit 3) axioms claims []
                    assertEqual "" expect actual
              where
                claims =
                    [ mkSomeClaim1 (Pattern.fromTermLike Mock.a) right []
                    , mkSomeClaim2 (Pattern.fromTermLike Mock.d) right []
                    ]
                stuck = mkSomeClaim1 (Pattern.fromTermLike Mock.c) right []
                expect = MultiAnd.singleton (StuckClaim stuck)
        in
        [ mkTest "OnePath" mkSomeClaimOnePath mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath mkSomeClaimAllPath
        , mkTest "OnePath, AllPath" mkSomeClaimOnePath mkSomeClaimAllPath
        , mkTest "AllPath, OnePath" mkSomeClaimAllPath mkSomeClaimOnePath
        ]
    , testGroup "does not prove second of two claims" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.b Mock.c
                , simpleAxiom Mock.d Mock.e
                ]
            right = OrPattern.fromTermLike Mock.c
            mkTest name mkSomeClaim1 mkSomeClaim2 =
                testCase name $ do
                    actual <- proveClaims_ Unlimited (Limit 3) axioms claims []
                    assertEqual "" expect actual
              where
                claims =
                    [ mkSomeClaim1 (Pattern.fromTermLike Mock.a) right []
                    , mkSomeClaim2 (Pattern.fromTermLike Mock.d) right []
                    ]
                stuck = mkSomeClaim2 (Pattern.fromTermLike Mock.e) right []
                expect = MultiAnd.singleton (StuckClaim stuck)
        in
        [ mkTest "OnePath" mkSomeClaimOnePath mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath mkSomeClaimAllPath
        , mkTest "OnePath, AllPath" mkSomeClaimOnePath mkSomeClaimAllPath
        , mkTest "AllPath, OnePath" mkSomeClaimAllPath mkSomeClaimOnePath
        ]
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
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
        assertEqual "" MultiAnd.top actual
    , testGroup "proves first claim circularly, but proving circularity fails" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.c Mock.d
                ]
            mkTest name mkSomeClaim =
                testCase name $ do
                    actual <- proveClaims_ Unlimited (Limit 4) axioms claims []
                    assertEqual "" expect actual
              where
                proven =
                    mkSomeClaim
                        (Pattern.fromTermLike Mock.a)
                        (OrPattern.fromTermLike Mock.d)
                        []
                circularity =
                    mkSomeClaim
                        (Pattern.fromTermLike Mock.b)
                        (OrPattern.fromTermLike Mock.c)
                        []
                claims = [proven, circularity]
                stuck = circularity
                expect = MultiAnd.singleton (StuckClaim stuck)
        in
        [ mkTest "OnePath" mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath
        , testCase "does not use different claim types" $ do
            actual <- proveClaims_
                Unlimited
                (Limit 4)
                axioms
                [ simpleOnePathClaim Mock.a Mock.d
                , simpleAllPathClaim Mock.b Mock.c
                ]
                []
            let stuck =
                    mkSomeClaimOnePath
                        (Pattern.fromTermLike Mock.b)
                        (OrPattern.fromTermLike Mock.d)
                        []
                expect = MultiAnd.singleton (StuckClaim stuck)
            assertEqual "" expect actual
        ]
    , testGroup "proves first claim with trusted circularity" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.c Mock.d
                ]
            proven mkSomeClaim =
                mkSomeClaim
                    (Pattern.fromTermLike Mock.a)
                    (OrPattern.fromTermLike Mock.d)
                    []
            trusted mkSomeClaim =
                mkSomeClaim
                    (Pattern.fromTermLike Mock.b)
                    (OrPattern.fromTermLike Mock.c)
                    []
                & makeTrusted
            mkTest name mkSomeClaim =
                testCase name $ do
                    actual <- proveClaims_ Unlimited (Limit 4) axioms claims []
                    assertEqual "" MultiAnd.top actual
              where
                claims = [proven mkSomeClaim, trusted mkSomeClaim]
        in
        [ mkTest "OnePath" mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath
        , testCase "does not use different claim types" $ do
            -- Axiom: a => b
            -- Axiom: c => d
            -- Claim: a => d
            -- Trusted Claim: b => c
            -- Expected: error b
            let claims = [proven mkSomeClaimOnePath, trusted mkSomeClaimAllPath]
            actual <- proveClaims_ Unlimited (Limit 4) axioms claims []
            let stuck =
                    mkSomeClaimOnePath
                        (Pattern.fromTermLike Mock.b)
                        (OrPattern.fromTermLike Mock.d)
                        []
                expect = MultiAnd.singleton (StuckClaim stuck)
            assertEqual "" expect actual
        ]
    , testGroup "prefer claims over axioms" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.b Mock.c
                , simpleAxiom Mock.c Mock.d
                ]
            proveable mkSomeClaim =
                mkSomeClaim
                    (Pattern.fromTermLike Mock.a)
                    (OrPattern.fromTermLike Mock.d)
                    []
            misdirection mkSomeClaim =
                mkSomeClaim
                    (Pattern.fromTermLike Mock.b)
                    (OrPattern.fromTermLike Mock.e)
                    []
            mkTest name mkSomeClaim =
                testCase name $ do
                    actual <- proveClaims_
                        Unlimited
                        (Limit 4)
                        axioms
                        claims
                        []
                    assertEqual "" expect actual
              where
                claims = [proveable mkSomeClaim, misdirection mkSomeClaim]
                stuck =
                    mkSomeClaim
                        (Pattern.fromTermLike Mock.e)
                        (OrPattern.fromTermLike Mock.d)
                        []
                expect = MultiAnd.singleton (StuckClaim stuck)
        in
        [ mkTest "OnePath" mkSomeClaimOnePath
        , mkTest "AllPath" mkSomeClaimAllPath
        ]
    , testGroup "one-path claim about non-deterministic axioms" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.a Mock.c
                ]
            claims mkSomeClaim =
                [ mkSomeClaim
                    (Pattern.fromTermLike Mock.a)
                    (OrPattern.fromTermLike Mock.b)
                    []
                ]
            claimsOnePath = claims mkSomeClaimOnePath
            claimsAllPath = claims mkSomeClaimAllPath
        in
        [ testCase "proves one-path claim" $ do
            actual <- proveClaims_ Unlimited (Limit 5) axioms claimsOnePath []
            assertEqual "" MultiAnd.top actual
        , testCase "does not prove all-path claim" $ do
            actual <- proveClaims_ Unlimited (Limit 5) axioms claimsAllPath []
            let stuck =
                    mkSomeClaimAllPath
                        (Pattern.fromTermLike Mock.c)
                        (OrPattern.fromTermLike Mock.b)
                        []
                expect = MultiAnd.singleton (StuckClaim stuck)
            assertEqual "" expect actual
        ]
    , testGroup "applies axioms in priority order" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claims = [mkSimpleClaim Mock.a Mock.d]

                    actual1 <- proveClaims_
                        Unlimited
                        Unlimited
                        [ simpleAxiom Mock.a Mock.b
                        , simplePriorityAxiom Mock.b Mock.c 2
                        , simplePriorityAxiom Mock.b Mock.d 1
                        ]
                        claims
                        []
                    assertEqual "succeeds with preferred axiom"
                        MultiAnd.top
                        actual1

                    actual2 <- proveClaims_
                        Unlimited
                        Unlimited
                        [ simpleAxiom Mock.a Mock.b
                        , simplePriorityAxiom Mock.b Mock.c 1
                        , simplePriorityAxiom Mock.b Mock.d 2
                        ]
                        claims
                        []
                    let stuck = mkSimpleClaim Mock.c Mock.d
                        expect = MultiAnd.singleton (StuckClaim stuck)
                    assertEqual "fails with preferred axiom" expect actual2
        in
        [ mkTest "OnePath" simpleOnePathClaim
        , mkTest "AllPath" simpleAllPathClaim
        ]
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
    -> IO StuckClaims
proveClaims_ breadthLimit depthLimit axioms claims alreadyProven =
    do
        ProveClaimsResult { stuckClaims } <-
            Test.Kore.Reachability.Prove.proveClaims
                breadthLimit
                depthLimit
                axioms
                claims
                alreadyProven
        pure stuckClaims
