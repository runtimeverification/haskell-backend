module Test.Kore.Reachability.Prove (
    test_proveClaims,
) where

import Data.Default (
    def,
 )
import Data.Limit (
    Limit (..),
 )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeEqualsPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRewritingPattern,
    mkRuleVariable,
 )
import Kore.Rewrite.RulePattern (
    RulePattern (..),
    injectTermIntoRHS,
    mkRewritingRule,
    rulePattern,
 )
import Kore.Rewrite.Strategy (
    GraphSearchOrder (..),
 )
import Kore.Unparser (
    unparseToText2,
 )
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_proveClaims :: [TestTree]
test_proveClaims =
    [ testGroup "runs zero steps with depth = 0" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 0)
                            [simpleAxiom Mock.a Mock.b]
                            [claim]
                            []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "runs zero steps with breadth = 0" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <-
                        proveClaims_
                            (Limit 0)
                            Unlimited
                            [simpleAxiom Mock.a Mock.b]
                            [claim]
                            []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "runs one step with depth = 1" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <-
                        proveClaims_
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
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "proves direct implication" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 1)
                            []
                            [mkSimpleClaim Mock.a Mock.a]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "does not prove implication without rewriting" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <-
                        proveClaims_
                            Unlimited
                            Unlimited
                            []
                            [claim]
                            []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "proves by rewriting into disjunction" $
        let mkTest name mkSomeClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            (Limit 2)
                            Unlimited
                            [simpleAxiom Mock.a Mock.b]
                            [ mkSomeClaim
                                (Pattern.fromTermLike Mock.a)
                                ( OrPattern.fromPatterns $
                                    map
                                        Pattern.fromTermLike
                                        [ Mock.b
                                        , Mock.c
                                        ]
                                )
                                []
                            ]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" mkSomeClaimOnePath
            , mkTest "AllPath" mkSomeClaimAllPath
            ]
    , testGroup "proves anything with cyclic rules" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 3)
                            [simpleAxiom Mock.a Mock.a]
                            [mkSimpleClaim Mock.a Mock.b]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "proves disjunction with non-deterministic rules" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.a Mock.c
                ]
            mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 2)
                            axioms
                            [mkSimpleClaim Mock.a (mkOr Mock.b Mock.c)]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "returns first stuck claim after disjunction" $
        let axioms = [simpleAxiom Mock.a (mkOr Mock.b Mock.c)]
            mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 1)
                            axioms
                            [mkSimpleClaim Mock.a Mock.d]
                            []
                    let stuck = mkSimpleClaim Mock.b Mock.d
                        expect = MultiAnd.singleton (StuckClaim stuck)
                    assertEqual "" expect actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "proves one claim" $
        let axioms = [simpleAxiom Mock.a Mock.b]
            mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 2)
                            axioms
                            [mkSimpleClaim Mock.a Mock.b]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "does not apply trusted claims in first step" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claim = mkSimpleClaim Mock.a Mock.b
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 4)
                            []
                            [makeTrusted claim, claim]
                            []
                    let expect = MultiAnd.singleton (StuckClaim claim)
                    assertEqual "" expect actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "proves claim with multiple rewrites" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.b Mock.c
                ]
            mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 3)
                            axioms
                            [mkSimpleClaim Mock.a Mock.c]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "stops rewriting when claim is proven" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.b Mock.c
                , simpleAxiom Mock.c Mock.d
                ]
            mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 3)
                            axioms
                            [mkSimpleClaim Mock.a Mock.c]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "proves claim with narrowed branch" $
        let axioms =
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
                , simpleAxiom
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                    Mock.b
                , simpleAxiom
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                ]
            mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 4)
                            axioms
                            [ mkSimpleClaim
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                                Mock.b
                            ]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "reports only failed branch of proof" $
        let stuckCondition =
                makeNotPredicate
                    ( makeEqualsPredicate
                        (mkElemVar Mock.x)
                        Mock.a
                    )
                    & Condition.fromPredicate
            stuckConfig =
                Pattern.withCondition
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                    stuckCondition
                    & mkRewritingPattern
            initialConfig =
                Mock.functionalConstr10 (mkElemVar Mock.x)
                    & Pattern.fromTermLike
                    & mkRewritingPattern
            finalConfigs = OrPattern.fromTermLike Mock.b
            axioms =
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
                , simpleAxiom
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                ]
            mkTest name mkSomeClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 3)
                            axioms
                            [mkSomeClaim initialConfig finalConfigs []]
                            []
                    let stuck = mkSomeClaim stuckConfig finalConfigs []
                        expect = MultiAnd.singleton (StuckClaim stuck)
                    assertEqual "" expect actual
         in [ mkTest "OnePath" mkSomeClaimOnePath
            , mkTest "AllPath" mkSomeClaimAllPath
            ]
    , testGroup "stops when breadth limit is exceeded" $
        let axioms =
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
                , simpleAxiom
                    (Mock.functionalConstr10 (mkElemVar Mock.x))
                    (Mock.functionalConstr11 (mkElemVar Mock.x))
                ]
            stuckConfigs =
                map
                    mkRewritingPattern
                    [ Pattern.withCondition
                        (Mock.functionalConstr11 (mkElemVar Mock.x))
                        ( Condition.fromPredicate
                            ( makeNotPredicate
                                ( makeEqualsPredicate
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
                    actual <-
                        proveClaims_
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
         in [ mkTest "OnePath" mkSomeClaimOnePath
            , mkTest "AllPath" mkSomeClaimAllPath
            ]
    , testGroup "proves two claims" $
        let axioms =
                [ simpleAxiom Mock.a Mock.b
                , simpleAxiom Mock.b Mock.c
                , simpleAxiom Mock.d Mock.e
                ]
            mkTest name mkSimpleClaim1 mkSimpleClaim2 =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 3)
                            axioms
                            [ mkSimpleClaim1 Mock.a Mock.c
                            , mkSimpleClaim2 Mock.d Mock.e
                            ]
                            []
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath, OnePath" simpleOnePathClaim simpleOnePathClaim
            , mkTest "OnePath, AllPath" simpleOnePathClaim simpleAllPathClaim
            , mkTest "AllPath, AllPath" simpleAllPathClaim simpleAllPathClaim
            , mkTest "AllPath, OnePath" simpleAllPathClaim simpleOnePathClaim
            ]
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
         in [ mkTest "OnePath" mkSomeClaimOnePath mkSomeClaimOnePath
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
         in [ mkTest "OnePath" mkSomeClaimOnePath mkSomeClaimOnePath
            , mkTest "AllPath" mkSomeClaimAllPath mkSomeClaimAllPath
            , mkTest "OnePath, AllPath" mkSomeClaimOnePath mkSomeClaimAllPath
            , mkTest "AllPath, OnePath" mkSomeClaimAllPath mkSomeClaimOnePath
            ]
    , testGroup "skips proven claim" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    actual <-
                        proveClaims_
                            Unlimited
                            (Limit 3)
                            []
                            [mkSimpleClaim Mock.a Mock.b]
                            [mkSimpleClaim Mock.a Mock.b]
                    assertEqual "" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
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
         in [ mkTest "OnePath" mkSomeClaimOnePath
            , mkTest "AllPath" mkSomeClaimAllPath
            , testCase "does not use different claim types" $ do
                actual <-
                    proveClaims_
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
         in [ mkTest "OnePath" mkSomeClaimOnePath
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
                    actual <-
                        proveClaims_
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
         in [ mkTest "OnePath" mkSomeClaimOnePath
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
         in [ testCase "proves one-path claim" $ do
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

                    actual1 <-
                        proveClaims_
                            Unlimited
                            Unlimited
                            [ simpleAxiom Mock.a Mock.b
                            , simplePriorityAxiom Mock.b Mock.c 2
                            , simplePriorityAxiom Mock.b Mock.d 1
                            ]
                            claims
                            []
                    assertEqual
                        "succeeds with preferred axiom"
                        MultiAnd.top
                        actual1

                    actual2 <-
                        proveClaims_
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
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    , testGroup "LHS is undefined" $
        let mkTest name mkSimpleClaim =
                testCase name $ do
                    let claims = [mkSimpleClaim mkBottom_ Mock.a]
                    actual <-
                        proveClaims_
                            Unlimited
                            Unlimited
                            []
                            claims
                            []
                    assertEqual "Result is \\top" MultiAnd.top actual
         in [ mkTest "OnePath" simpleOnePathClaim
            , mkTest "AllPath" simpleAllPathClaim
            ]
    ]

simpleAxiom ::
    TermLike VariableName ->
    TermLike VariableName ->
    Rule SomeClaim
simpleAxiom left right =
    ReachabilityRewriteRule $ simpleRewrite left right

simpleClaim ::
    TermLike VariableName ->
    TermLike VariableName ->
    ClaimPattern
simpleClaim
    (TermLike.mapVariables (pure mkRuleVariable) -> left)
    (TermLike.mapVariables (pure mkRuleVariable) -> right) =
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

simpleOnePathClaim ::
    TermLike VariableName ->
    TermLike VariableName ->
    SomeClaim
simpleOnePathClaim left right =
    OnePath . OnePathClaim $ simpleClaim left right

simpleAllPathClaim ::
    TermLike VariableName ->
    TermLike VariableName ->
    SomeClaim
simpleAllPathClaim left right =
    AllPath . AllPathClaim $ simpleClaim left right

simplePriorityAxiom ::
    TermLike VariableName ->
    TermLike VariableName ->
    Integer ->
    Rule SomeClaim
simplePriorityAxiom left right priority =
    ReachabilityRewriteRule . mkRewritingRule . RewriteRule $
        RulePattern
            { left = left
            , antiLeft = Nothing
            , requires = makeTruePredicate
            , rhs = injectTermIntoRHS right
            , attributes =
                def
                    { Attribute.priority = Attribute.Priority (Just priority)
                    }
            }

simpleRewrite ::
    TermLike VariableName ->
    TermLike VariableName ->
    RewriteRule RewritingVariableName
simpleRewrite left right =
    mkRewritingRule $ RewriteRule $ rulePattern left right

proveClaims ::
    Limit Natural ->
    Limit Natural ->
    [Rule SomeClaim] ->
    [SomeClaim] ->
    [SomeClaim] ->
    IO ProveClaimsResult
proveClaims breadthLimit depthLimit axioms claims alreadyProven =
    Kore.Reachability.proveClaims
        breadthLimit
        BreadthFirst
        (AllClaims claims)
        (Axioms axioms)
        (AlreadyProven (map unparseToText2 alreadyProven))
        (ToProve (map applyDepthLimit . selectUntrusted $ claims))
        & runSimplifierSMT mockEnv
  where
    mockEnv = Mock.env
    applyDepthLimit claim = (claim, depthLimit)
    selectUntrusted = filter (not . isTrusted)

proveClaims_ ::
    Limit Natural ->
    Limit Natural ->
    [Rule SomeClaim] ->
    [SomeClaim] ->
    [SomeClaim] ->
    IO StuckClaims
proveClaims_ breadthLimit depthLimit axioms claims alreadyProven =
    do
        ProveClaimsResult{stuckClaims} <-
            Test.Kore.Reachability.Prove.proveClaims
                breadthLimit
                depthLimit
                axioms
                claims
                alreadyProven
        pure stuckClaims
