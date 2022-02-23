module Test.Kore.Simplify.Inj (
    test_simplify,
) where

import Kore.Internal.Inj
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.SideCondition.SideCondition qualified as SideCondition (
    mkRepresentation,
 )
import Kore.Internal.Symbol
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkElementConfigVariable,
 )
import Kore.Simplify.Inj qualified as Kore
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify (
    runSimplifier,
 )
import Test.Tasty
import Test.Tasty.HUnit

test_simplify :: [TestTree]
test_simplify =
    [ test
        "inj{test, top}(a)"
        [Mock.a & TermLike.markSimplified & Pattern.fromTermLike]
        [Mock.sortInjection Mock.topSort Mock.a & Pattern.fromTermLike]
    , test
        "inj{test, top}(x:test)"
        [TermLike.mkElemVar x & TermLike.markSimplified & Pattern.fromTermLike]
        [ Mock.sortInjection Mock.topSort (TermLike.mkElemVar x)
            & Pattern.fromTermLike
        ]
    ]
  where
    x = mkElementConfigVariable Mock.x

    repr =
        SideCondition.mkRepresentation
            (SideCondition.top @RewritingVariableName)

    injFrom = Mock.testSort
    injTo = Mock.topSort
    Symbol{symbolConstructor = injConstructor} = symbol'
    Symbol{symbolAttributes = injAttributes} = symbol'
    symbol' = Mock.sortInjectionSymbol injFrom injTo
    mkInj injChild =
        Inj
            { injConstructor
            , injFrom
            , injTo
            , injAttributes
            , injChild
            }

    test ::
        HasCallStack =>
        TestName ->
        [Pattern RewritingVariableName] ->
        [Pattern RewritingVariableName] ->
        TestTree
    test testName preInput preExpect =
        testCase testName $ do
            let input = mkInj (OrPattern.fromPatterns preInput)
                expect = OrPattern.fromPatterns preExpect
            actual <- simplify input
            (assertBool "Expected simplified patterns")
                (OrPattern.isSimplified repr actual)
            assertEqual "" expect actual

simplify ::
    Inj (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
simplify injOrPattern =
    Kore.simplify injOrPattern
        & runSimplifier Mock.env
