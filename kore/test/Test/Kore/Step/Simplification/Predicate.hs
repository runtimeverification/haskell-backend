module Test.Kore.Step.Simplification.Predicate (
    test_simplify,
) where

import Kore.Internal.From
import Kore.Internal.MultiAnd (MultiAnd)
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (TermLike)
import Kore.Rewriting.RewritingVariable
import Kore.Step.Simplification.Predicate (simplify)
import Prelude.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty
import Test.Tasty.HUnit

test_simplify :: [TestTree]
test_simplify =
    [ test
        "\\and(_, _)"
        (fromAnd faCeil fbCeil)
        [MultiAnd.make [faCeil, fbCeil]]
    , test
        "\\and(\\top, _)"
        (fromAnd fromTop_ faCeil)
        [MultiAnd.make [faCeil]]
    , test
        "\\and(\\bottom, _)"
        (fromAnd fromBottom_ faCeil)
        []
    , test
        "\\or(_, _)"
        (fromOr faCeil fbCeil)
        [MultiAnd.singleton faCeil, MultiAnd.singleton fbCeil]
    , test
        "\\or(\\bottom, _)"
        (fromOr fromBottom_ faCeil)
        [MultiAnd.singleton faCeil]
    , test
        "\\or(\\top, _)"
        (fromOr fromTop_ faCeil)
        [MultiAnd.top]
    ]
  where
    test ::
        TestName ->
        Predicate RewritingVariableName ->
        [MultiAnd (Predicate RewritingVariableName)] ->
        TestTree
    test testName input expect =
        testCase testName $ do
            actual <-
                simplify SideCondition.top input
                    & Test.runSimplifierBranch Mock.env
            assertEqual "" expect actual

    fa, fb :: TermLike RewritingVariableName
    fa = Mock.f Mock.a
    fb = Mock.f Mock.b

    faCeil, fbCeil :: Predicate RewritingVariableName
    faCeil = fromCeil_ fa
    fbCeil = fromCeil_ fb
