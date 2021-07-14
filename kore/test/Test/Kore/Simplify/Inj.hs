module Test.Kore.Simplify.Inj (
    test_simplify,
) where

import Kore.Internal.Inj
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    mkRepresentation,
 )
import Kore.Internal.Symbol
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkElementConfigVariable,
 )
import qualified Kore.Simplify.Inj as Kore
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
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
