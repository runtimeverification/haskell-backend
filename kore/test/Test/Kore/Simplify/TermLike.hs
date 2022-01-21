module Test.Kore.Simplify.TermLike (
    test_simplify_sideConditionReplacements,
    test_simplifyOnly,
) where

import Control.Monad.Catch (
    MonadThrow,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeEqualsPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
    mkRepresentation,
 )
import Kore.Internal.TermLike
import qualified Kore.Rewrite.Function.Memo as Memo
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    getRewritingPattern,
    mkConfigVariable,
    mkElementConfigVariable,
    mkRewritingTerm,
 )
import Kore.Simplify.Simplify
import qualified Kore.Simplify.TermLike as TermLike
import qualified Logic
import Prelude.Kore
import qualified Pretty
import qualified Test.Kore.Rewrite.MockSymbols as Mock
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
            <$> runSimplifier Mock.env
                . TermLike.simplify sideCondition
                . mkRewritingTerm

newtype TestSimplifier a = TestSimplifier {getTestSimplifier :: SimplifierT NoSMT a}
    deriving newtype (Functor, Applicative, Monad)
    deriving newtype (MonadLog, MonadSMT, MonadThrow)

instance MonadSimplify TestSimplifier where
    askMetadataTools = TestSimplifier askMetadataTools
    askSimplifierAxioms = TestSimplifier askSimplifierAxioms
    localSimplifierAxioms f =
        TestSimplifier . localSimplifierAxioms f . getTestSimplifier
    askMemo = TestSimplifier (Memo.liftSelf TestSimplifier <$> askMemo)
    askInjSimplifier = TestSimplifier askInjSimplifier
    askOverloadSimplifier = TestSimplifier askOverloadSimplifier
    askSimplifierXSwitch = TestSimplifier askSimplifierXSwitch
    getCache = TestSimplifier getCache
    putCache = TestSimplifier . putCache
    simplifyCondition sideCondition condition =
        Logic.mapLogicT
            TestSimplifier
            (simplifyCondition sideCondition condition)

    -- Throw an error if any pattern/term would be simplified.
    simplifyPattern = undefined
    simplifyTerm = undefined

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
    runSimplifier Mock.env
        . TermLike.simplify SideCondition.top
