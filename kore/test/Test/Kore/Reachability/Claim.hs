module Test.Kore.Reachability.Claim (
    test_checkImplication,
    test_checkSimpleImplication,
    test_simplifyRightHandSide,
) where

import Control.Lens qualified as Lens
import Control.Monad.Except (runExceptT)
import Data.Generics.Product (
    field,
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
import Kore.Reachability.Claim (
    CheckImplicationResult (..),
    checkImplicationWorker,
    checkSimpleImplication,
    simplifyRightHandSide,
 )
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
    mkClaimPattern,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
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
            goal = mkGoal config dest existentials
        actual <-
            checkImplication goal
        assertEqual "" [Implied goal] actual
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
        assertEqual "" [Implied goal] actual
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
        assertEqual "" [Implied goal] actual
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
        assertEqual "" [Implied goal] actual
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
        assertEqual "" [Implied goal] actual
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
        assertEqual "" [Implied goal] actual
    ]

test_checkSimpleImplication :: [TestTree]
test_checkSimpleImplication =
    [ testCase "Variable unification" $ do
        let config = mkElemVar Mock.x & Pattern.fromTermLike
            dest = mkElemVar Mock.y & Pattern.fromTermLike
            existentials = [Mock.y]
            goal = mkGoal config (OrPattern.fromPattern dest) existentials
            subst = mkSubst (inject Mock.x) (mkElemVar Mock.y)
        actual <-
            checkSimple config dest existentials
        assertEqual "" (Implied (goal, Just subst)) actual
    , testCase "does not unify" $ do
        actual <-
            checkSimple (Pattern.fromTermLike Mock.a) (Pattern.fromTermLike Mock.b) []
        assertEqual "" (NotImplied (aToB, Nothing)) actual
    , testCase "does not unify, with left condition" $ do
        let goal =
                mkGoal
                    -- simplification turns the predicate into a substitution
                    (Pattern.assign (inject Mock.x) Mock.a)
                    (OrPattern.fromTermLike Mock.b)
                    []
        actual <-
            checkSimple
                ( Pattern.fromTermAndPredicate
                    Mock.a
                    (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
                )
                (Pattern.fromTermLike Mock.b)
                []
        assertEqual "" (NotImplied (goal, Nothing)) actual
    , testCase "does not unify, with right condition" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest =
                Pattern.withCondition
                    Mock.b
                    (makeEqualsPredicate (mkElemVar Mock.x) Mock.a & from)
            result =
                Pattern.withCondition
                    Mock.b
                    -- simplification turns the predicate into a substitution
                    (Condition.assign (inject Mock.x) Mock.a)
            existentials = [Mock.x]
            goal = mkGoal config (OrPattern.fromPattern result) existentials
        actual <-
            checkSimple config dest existentials
        assertEqual "" (NotImplied (goal, Nothing)) actual
    , testCase "Variable unification, conditions match" $ do
        -- FIXME this matches trivially now since simplification
        -- applies the substitutions
        let config =
                Pattern.withCondition
                    (mkElemVar Mock.x)
                    (Condition.assign (inject Mock.x) Mock.a)
            dest =
                Pattern.withCondition
                    (mkElemVar Mock.y)
                    (Condition.assign (inject Mock.y) Mock.a)
            existentials = [Mock.y]
            goal =
                mkGoal
                    -- simplification applies the substitutions
                    (Pattern.fromTermLike Mock.a <* config) -- ((Pattern.fromTermLike Mock.a) <> config)
                    (OrPattern.fromPattern (Pattern.fromTermLike Mock.a <* dest))
                    existentials
            subst = mempty -- FIXME WAS mkSubst (inject Mock.x) (mkElemVar Mock.y)
        actual <- checkSimple config dest existentials
        assertEqual "" (Implied (goal, Just subst)) actual
    , -- FIXME test below changes target. When simplification applies
      -- substitutions the terms do not unify any more in this test
      -- , testCase "Variable unification, conditions don't match" $ do
      --     let config =
      --             Pattern.withCondition
      --                 (mkElemVar Mock.x)
      --                 (Condition.assign (inject Mock.x) Mock.a)
      --         dest =
      --             Pattern.withCondition
      --                 (mkElemVar Mock.y)
      --                 (Condition.assign (inject Mock.y) Mock.b)
      --         existentials = [Mock.y]
      --         -- goal = mkGoal config (OrPattern.fromPattern dest) existentials
      --         stuckConfig =
      --             Pattern.withCondition
      --                 Mock.a
      --                 (Condition.assign (inject Mock.x) Mock.a)
      --         stuckGoal =
      --             mkGoal stuckConfig (OrPattern.fromPattern dest) existentials
      --         subst = mkSubst (inject Mock.x) (mkElemVar Mock.y)
      --     actual <- checkSimple config dest existentials
      --     assertEqual "" (NotImpliedStuck (stuckGoal, Just subst)) actual
      testCase "Function unification, definedness condition and remainder" $ do
        let config = Mock.f (mkElemVar Mock.x) & Pattern.fromTermLike
            dest = Mock.f (mkElemVar Mock.y) & Pattern.fromTermLike
            existentials = [Mock.y]
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
                mkGoal stuckConfig (OrPattern.fromPattern dest) existentials
        actual <- checkSimple config dest existentials
        assertEqual "" (NotImpliedStuck (stuckGoal, Just mempty)) actual
    , -- FIXME test below not supported any more. Pattern simplification
      -- distributes the branch and yields a non-singleton Or-pattern
      -- , testCase "Branching RHS with condition in single pattern" $ do
      --     let config = Mock.a & Pattern.fromTermLike
      --         dest =
      --             Pattern.fromTermAndPredicate
      --                 (mkElemVar Mock.x)
      --                 ( makeOrPredicate
      --                     ( makeEqualsPredicate
      --                         (mkElemVar Mock.x)
      --                         Mock.a
      --                     )
      --                     ( makeEqualsPredicate
      --                         (mkElemVar Mock.x)
      --                         Mock.b
      --                     )
      --                 )
      --         existentials = [Mock.x]
      --         goal = mkGoal config (OrPattern.fromPattern dest) existentials
      --         subst = mkSubst (inject Mock.x) Mock.a
      --     actual <- checkSimple config dest existentials
      --     assertEqual "" (Implied (goal, Just subst)) actual
      testCase "Stuck if RHS is \\bottom" $ do
        let config = Mock.a & Pattern.fromTermLike
            dest = Pattern.bottomOf Mock.topSort
            goal = mkGoal config (OrPattern.bottom) []
        actual <- checkSimple config dest []
        assertEqual "" (NotImplied (goal, Nothing)) actual
    , testCase "Implied if both sides are \\bottom" $ do
        let config = Pattern.bottomOf Mock.topSort
            dest = Pattern.bottomOf Mock.topSort
            goal = mkGoal config (OrPattern.fromPattern dest) []
        actual <- checkSimple config dest []
        assertEqual "" (Implied (goal, Just mempty)) actual
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

mkSubst ::
    TermLike.SomeVariable VariableName ->
    TermLike.TermLike VariableName ->
    Substitution.Substitution RewritingVariableName
mkSubst var term =
    Substitution.mapVariables (pure mkConfigVariable) $
        Substitution.wrap
            [Substitution.assign var term]

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

checkSimple ::
    Pattern VariableName ->
    Pattern VariableName ->
    [ElementVariable VariableName] ->
    IO
        ( CheckImplicationResult
            ( ClaimPattern
            , Maybe (Substitution.Substitution RewritingVariableName)
            )
        )
checkSimple left right existentials =
    fmap (either (error . show) id)
        . runSimplifierSMT Mock.env
        . runExceptT
        $ checkSimpleImplication
            (mkRewritingPattern left)
            (mkRewritingPattern right)
            (fmap (TermLike.mapElementVariable (pure mkConfigVariable)) existentials)
