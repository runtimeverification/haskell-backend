module Test.Kore.Simplify.InternalSet (
    test_simplify,
) where

import qualified Data.HashMap.Strict as HashMap
import Data.Maybe (
    fromJust,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalSet
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.InternalSet (
    simplify,
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ becomes "\\bottom element" (mkSet [bottom] []) []
    , becomes "\\bottom term" (mkSet [] [bottom]) []
    , becomes "duplicate key" (mkSet [a, a] []) []
    , becomes
        "single opaque elem"
        (mkSet [] [a])
        [Mock.a & Pattern.fromTermLike]
    , becomes
        "distributes \\or element"
        (mkSet [a <> b] [])
        [ mkSetAux [Mock.a] [] []
            & mkInternalSet
            & Pattern.fromTermLike
        , mkSetAux [Mock.b] [] []
            & mkInternalSet
            & Pattern.fromTermLike
        ]
    , becomes
        "distributes \\or compound"
        (mkSet [a] [a <> b])
        [ mkSetAux [Mock.a] [] [Mock.a]
            & mkInternalSet
            & Pattern.fromTermLike
        , mkSetAux [Mock.a] [] [Mock.b]
            & mkInternalSet
            & Pattern.fromTermLike
        ]
    , becomes
        "collects \\and"
        ( mkSet [Pattern.withCondition Mock.a ceila] []
            & fmap OrPattern.fromPattern
        )
        [Pattern.withCondition (mkSetAux [Mock.a] [] [] & mkInternalSet) ceila]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    ceila =
        makeCeilPredicate (Mock.f Mock.a)
            & Condition.fromPredicate
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes ::
        HasCallStack =>
        TestName ->
        InternalSet Key (OrPattern RewritingVariableName) ->
        [Pattern RewritingVariableName] ->
        TestTree
    becomes name origin (OrPattern.fromPatterns -> expects) =
        testCase name $ do
            let actuals = evaluate origin
            assertEqual "" expects actuals

mkSet :: [child] -> [child] -> InternalSet Key child
mkSet = mkSetAux []

mkSetAux ::
    [TermLike Concrete] ->
    [child] ->
    [child] ->
    InternalSet Key child
mkSetAux concreteElements elements opaque =
    InternalAc
        { builtinAcSort = Mock.setSort
        , builtinAcUnit = Mock.unitSetSymbol
        , builtinAcElement = Mock.elementSetSymbol
        , builtinAcConcat = Mock.concatSetSymbol
        , builtinAcChild =
            NormalizedSet
                NormalizedAc
                    { elementsWithVariables = SetElement <$> elements
                    , concreteElements =
                        concreteElements
                            & map (retractKey >>> fromJust >>> mkSetValue)
                            & HashMap.fromList
                    , opaque
                    }
        }
  where
    mkSetValue = \x -> (x, SetValue)

evaluate ::
    InternalSet Key (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify
