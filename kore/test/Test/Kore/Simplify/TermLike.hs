module Test.Kore.Simplify.TermLike (
    test_simplify_sideConditionReplacements,
    test_simplifyOnly,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeEqualsPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.SideCondition.SideCondition qualified as SideCondition (
    Representation,
    mkRepresentation,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    getRewritingPattern,
    mkConfigVariable,
    mkElementConfigVariable,
    mkRewritingTerm,
 )
import Kore.Simplify.TermLike qualified as TermLike
import Prelude.Kore
import Pretty qualified
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit

test_simplify_sideConditionReplacements :: [TestTree]
test_simplify_sideConditionReplacements =
    [ testCase "Replaces top level term" $ do
        let sideCondition =
                f a `equals` b
                    & SideCondition.fromPredicateWithReplacements
            term = f a
            expected = b & OrPattern.fromTermLike
        actual <-
            simplifyWithSideCondition
                sideCondition
                term
        assertEqual "" expected actual
    , testCase "Replaces nested term" $ do
        let sideCondition =
                f a `equals` b
                    & SideCondition.fromPredicateWithReplacements
            term = g (f a)
            expected = g b & OrPattern.fromTermLike
        actual <-
            simplifyWithSideCondition
                sideCondition
                term
        assertEqual "" expected actual
    , testCase "Replaces terms in sequence" $ do
        let sideCondition =
                (f a `equals` g b) `and'` (g b `equals` c)
                    & SideCondition.fromPredicateWithReplacements
            term = f a
            expected = c & OrPattern.fromTermLike
        actual <-
            simplifyWithSideCondition
                sideCondition
                term
        assertEqual "" expected actual
    , testCase "Replaces top level term after replacing subterm" $ do
        let sideCondition =
                (f a `equals` b) `and'` (g b `equals` c)
                    & SideCondition.fromPredicateWithReplacements
            term = g (f a)
            expected = c & OrPattern.fromTermLike
        actual <-
            simplifyWithSideCondition
                sideCondition
                term
        assertEqual "" expected actual
    ]
  where
    f = Mock.f
    g = Mock.g
    a = Mock.a
    b = Mock.b
    c = Mock.c
    equals = makeEqualsPredicate
    and' = makeAndPredicate

simplifyWithSideCondition ::
    SideCondition VariableName ->
    TermLike VariableName ->
    IO (OrPattern VariableName)
simplifyWithSideCondition
    (SideCondition.mapVariables (pure mkConfigVariable) -> sideCondition) =
        fmap (OrPattern.map getRewritingPattern)
            <$> testRunSimplifier Mock.env
                . TermLike.simplify sideCondition
                . mkRewritingTerm

test_simplifyOnly :: [TestTree]
test_simplifyOnly =
    [ (test "LIST.List \\and simplification failure")
        (mkAnd (Mock.concatList (mkTop Mock.listSort) (mkTop Mock.listSort)) (Mock.builtinList []))
        expectUnsimplified
    , (test "Non-function symbol without evaluators")
        Mock.plain00Subsort
        (expectTerm Mock.plain00Subsort)
    , (test "\\rewrites - simplified children")
        ( mkRewrites
            (mkBottom Mock.topSort)
            (mkCeil Mock.topSort Mock.unitSet)
        )
        expectUnsimplified
    , (test "Sort injection")
        (Mock.sortInjection Mock.topSort (mkElemVar x))
        (expectTerm $ Mock.sortInjection Mock.topSort (mkElemVar x))
    , (test "Sort injection - Nested")
        ( Mock.sortInjection
            Mock.topSort
            (Mock.sortInjection Mock.subSort Mock.aSubSubsort)
        )
        (expectTerm $ Mock.sortInjection Mock.topSort Mock.aSubSubsort)
    , (test "Variable")
        (mkElemVar x)
        (expectTerm $ mkElemVar x)
    ]
  where
    expectUnsimplified = Nothing
    expectTerm termLike = Just (OrPattern.fromTermLike termLike)

    x = mkElementConfigVariable Mock.x

    test ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        -- Expected output, if simplified.
        Maybe (OrPattern RewritingVariableName) ->
        TestTree
    test testName input maybeExpect =
        testCase testName $ do
            let expect = fromMaybe (OrPattern.fromTermLike input) maybeExpect
            actual <- simplify input
            let message =
                    (show . Pretty.vsep)
                        [ "Expected:"
                        , (Pretty.indent 4) (Pretty.pretty expect)
                        , "Actually:"
                        , (Pretty.indent 4) (Pretty.pretty actual)
                        ]
            assertEqual message expect actual
            (assertBool "Expected simplified pattern")
                (isNothing maybeExpect || OrPattern.isSimplified repr actual)

    repr :: SideCondition.Representation
    repr =
        SideCondition.mkRepresentation
            (SideCondition.top @RewritingVariableName)

simplify ::
    TermLike RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
simplify =
    testRunSimplifier Mock.env
        . TermLike.simplify SideCondition.top
