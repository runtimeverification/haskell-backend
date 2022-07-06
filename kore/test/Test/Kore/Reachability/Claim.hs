module Test.Kore.Reachability.Claim (
    test_checkImplication,
    test_simplifyRightHandSide,
) where

import Control.Lens qualified as Lens
import Data.Generics.Product (
    field,
 )
import Kore.Claim.Claim (
    CheckImplicationResult (..),
    checkImplicationWorker,
    simplifyRightHandSide,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeExistsPredicate,
    makeNotPredicate,
    makeOrPredicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike (
    ElementVariable,
    VariableName,
    mkElemVar,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.ClaimPattern (
    ClaimPattern,
    mkClaimPattern,
 )
import Kore.Rewrite.RewritingVariable (
    mkConfigVariable,
    mkRewritingPattern,
 )
import Logic qualified
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify (
    runSimplifierSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_checkImplication :: [TestTree]
test_checkImplication =
    [ testCase "Variable unification" $ do
        let config = mkElemVar Mock.x & Pattern.fromTermLike
            dest = mkElemVar Mock.y & OrPattern.fromTermLike
            existentials = [Mock.y]
        actual <-
            checkImplication (mkGoal config dest existentials)
        assertEqual "" [Implied] actual
    , testCase "does not unify" $ do
        let goal = aToB
        actual <-
            checkImplication goal
        assertEqual "" [NotImplied goal] actual
    , testCase "does not unify, with left condition" $ do
        let goal =
                Lens.over
                    (field @"left")
                    ( flip
                        Pattern.andCondition
                        ( makeEqualsPredicate (mkElemVar Mock.x) Mock.a
                            & Predicate.mapVariables (pure mkConfigVariable)
                            & from
                        )
                    )
                    aToB
        actual <-
            checkImplication goal
        assertEqual "" [NotImplied goal] actual
    , testCase "does not unify, with right condition" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest =
                Pattern.withCondition
                    Mock.b
                    (makeEqualsPredicate (mkElemVar Mock.x) Mock.a & from)
                    & OrPattern.fromPattern
            existentials = [Mock.x]
            goal = mkGoal config dest existentials
        actual <-
            checkImplication goal
        assertEqual "" [NotImplied goal] actual
    , testCase "Variable unification, conditions match" $ do
        let config =
                Pattern.withCondition
                    (mkElemVar Mock.x)
                    ( Substitution.wrap
                        [Substitution.assign (inject Mock.x) Mock.a]
                        & Condition.fromSubstitution
                    )
            dest =
                Pattern.withCondition
                    (mkElemVar Mock.y)
                    ( Substitution.wrap
                        [Substitution.assign (inject Mock.y) Mock.a]
                        & Condition.fromSubstitution
                    )
                    & OrPattern.fromPattern
            existentials = [Mock.y]
            goal = mkGoal config dest existentials
        actual <- checkImplication goal
        assertEqual "" [Implied] actual
    , testCase "Variable unification, conditions don't match" $ do
        let config =
                Pattern.withCondition
                    (mkElemVar Mock.x)
                    ( Substitution.wrap
                        [Substitution.assign (inject Mock.x) Mock.a]
                        & Condition.fromSubstitution
                    )
            dest =
                Pattern.withCondition
                    (mkElemVar Mock.y)
                    ( Substitution.wrap
                        [Substitution.assign (inject Mock.y) Mock.b]
                        & Condition.fromSubstitution
                    )
                    & OrPattern.fromPattern
            existentials = [Mock.y]
            goal = mkGoal config dest existentials
            stuckConfig =
                Pattern.withCondition
                    Mock.a
                    (Condition.assign (inject Mock.x) Mock.a)
            stuckGoal =
                mkGoal stuckConfig dest existentials
        actual <- checkImplication goal
        assertEqual "" [NotImpliedStuck stuckGoal] actual
    , testCase "Function unification, definedness condition and remainder" $ do
        let config = Mock.f (mkElemVar Mock.x) & Pattern.fromTermLike
            dest =
                Mock.f (mkElemVar Mock.y) & Pattern.fromTermLike
                    & OrPattern.fromPattern
            existentials = [Mock.y]
            goal = mkGoal config dest existentials
            stuckConfig =
                Pattern.fromTermAndPredicate
                    (Mock.f (mkElemVar Mock.x))
                    ( makeAndPredicate
                        ( makeCeilPredicate
                            (Mock.f (mkElemVar Mock.x))
                        )
                        ( makeNotPredicate
                            ( makeExistsPredicate
                                Mock.y
                                ( makeEqualsPredicate
                                    (Mock.f (mkElemVar Mock.x))
                                    (Mock.f (mkElemVar Mock.y))
                                )
                            )
                        )
                    )
            stuckGoal =
                mkGoal stuckConfig dest existentials
        actual <- checkImplication goal
        assertEqual "" [NotImpliedStuck stuckGoal] actual
    , testCase "Branching RHS" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest =
                [ Mock.a & Pattern.fromTermLike
                , Mock.b & Pattern.fromTermLike
                ]
                    & OrPattern.fromPatterns
            existentials = []
            goal = mkGoal config dest existentials
        actual <- checkImplication goal
        assertEqual "" [Implied] actual
    , testCase "Branching RHS with condition 1" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest =
                [ Pattern.fromTermAndPredicate
                    (mkElemVar Mock.x)
                    ( makeEqualsPredicate
                        (mkElemVar Mock.x)
                        Mock.a
                    )
                , Pattern.fromTermAndPredicate
                    (mkElemVar Mock.x)
                    ( makeEqualsPredicate
                        (mkElemVar Mock.x)
                        Mock.b
                    )
                ]
                    & OrPattern.fromPatterns
            existentials = [Mock.x]
            goal = mkGoal config dest existentials
        actual <- checkImplication goal
        assertEqual "" [Implied] actual
    , testCase "Branching RHS with condition 2" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest =
                Pattern.fromTermAndPredicate
                    (mkElemVar Mock.x)
                    ( makeOrPredicate
                        ( makeEqualsPredicate
                            (mkElemVar Mock.x)
                            Mock.a
                        )
                        ( makeEqualsPredicate
                            (mkElemVar Mock.x)
                            Mock.b
                        )
                    )
                    & OrPattern.fromPattern
            existentials = [Mock.x]
            goal = mkGoal config dest existentials
        actual <- checkImplication goal
        assertEqual "" [Implied] actual
    , testCase "Stuck if RHS is \\bottom" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest = OrPattern.bottom
            goal = mkGoal config dest []
        actual <- checkImplication goal
        assertEqual "" [NotImpliedStuck goal] actual
    , testCase "Implied if both sides are \\bottom" $ do
        let config = Pattern.bottomOf Mock.topSort
            dest = OrPattern.bottom
            goal = mkGoal config dest []
        actual <- checkImplication goal
        assertEqual "" [Implied] actual
    ]

test_simplifyRightHandSide :: [TestTree]
test_simplifyRightHandSide =
    [ testCase "Unsatisfiable branch gets pruned" $ do
        let unsatisfiableBranch =
                Pattern.fromTermAndPredicate
                    Mock.b
                    ( makeEqualsPredicate
                        (TermLike.mkTop Mock.boolSort)
                        (Mock.builtinInt 3 `Mock.lessInt` Mock.builtinInt 2)
                    )
            claim =
                mkGoal
                    (Pattern.topOf Mock.testSort)
                    ( [Pattern.fromTermLike Mock.a, unsatisfiableBranch]
                        & OrPattern.fromPatterns
                    )
                    []
            expected =
                mkGoal
                    (Pattern.topOf Mock.testSort)
                    (Mock.a & OrPattern.fromTermLike)
                    []
        actual <-
            simplifyRightHandSide
                id
                SideCondition.top
                claim
                & runSimplifierSMT Mock.env
        assertEqual "" expected actual
    ]

mkGoal ::
    Pattern VariableName ->
    OrPattern VariableName ->
    [ElementVariable VariableName] ->
    ClaimPattern
mkGoal
    (mkRewritingPattern -> leftPatt)
    (OrPattern.map mkRewritingPattern -> rightPatts)
    ( fmap (TermLike.mapElementVariable (pure mkConfigVariable)) ->
            existentialVars
        ) =
        mkClaimPattern leftPatt rightPatts existentialVars

aToB :: ClaimPattern
aToB =
    mkGoal
        (Mock.a & Pattern.fromTermLike)
        (Mock.b & OrPattern.fromTermLike)
        []

checkImplication :: ClaimPattern -> IO [CheckImplicationResult ClaimPattern]
checkImplication claim =
    checkImplicationWorker claim
        & Logic.observeAllT
        & runSimplifierSMT Mock.env
