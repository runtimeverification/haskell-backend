{-# LANGUAGE Strict #-}

module Test.Kore.Step.Simplification.InternalMap (
    test_simplify,
    test_unparse,
) where

import Prelude.Kore

import Test.Tasty

import Control.DeepSeq (
    force,
 )
import qualified Control.Exception as Exception (
    evaluate,
 )
import Control.Monad (
    void,
 )
import Data.Bifunctor (
    bimap,
 )
import qualified Data.Map.Strict as Map
import Data.Maybe (
    fromJust,
 )

import Kore.Attribute.Concat
import Kore.Attribute.Element
import Kore.Attribute.Unit
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalMap
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
import Kore.Step.Simplification.InternalMap (
    simplify,
 )
import Kore.Unparser

import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

shouldSucceed :: Bool
shouldSucceed = True

shouldFail :: Bool
shouldFail = False

withUnit :: Bool
withUnit = True

withoutUnit :: Bool
withoutUnit = False

withElement :: Bool
withElement = True

withoutElement :: Bool
withoutElement = False

withConcat :: Bool
withConcat = True

withoutConcat :: Bool
withoutConcat = False

test_simplify :: [TestTree]
test_simplify =
    [ becomes "\\bottom value" (mkMap [(a, bottom)] []) []
    , becomes "\\bottom key" (mkMap [(bottom, a)] []) []
    , becomes "\\bottom term" (mkMap [(a, b)] [bottom]) []
    , becomes "duplicate key" (mkMap [(a, b), (a, c)] []) []
    , becomes
        "single opaque elem"
        (mkMap [] [a])
        [Mock.a & Pattern.fromTermLike]
    , becomes
        "distributes \\or key"
        (mkMap [(a <> b, c)] [])
        [ mkMapAux [(Mock.a, Mock.c)] [] []
            & mkInternalMap
            & Pattern.fromTermLike
        , mkMapAux [(Mock.b, Mock.c)] [] []
            & mkInternalMap
            & Pattern.fromTermLike
        ]
    , becomes
        "distributes \\or value"
        (mkMap [(a, b <> c)] [])
        [ mkMapAux [(Mock.a, Mock.b)] [] []
            & mkInternalMap
            & Pattern.fromTermLike
        , mkMapAux [(Mock.a, Mock.c)] [] []
            & mkInternalMap
            & Pattern.fromTermLike
        ]
    , becomes
        "distributes \\or compound"
        (mkMap [(a, b)] [a <> b])
        [ mkMapAux [(Mock.a, Mock.b)] [] [Mock.a]
            & mkInternalMap
            & Pattern.fromTermLike
        , mkMapAux [(Mock.a, Mock.b)] [] [Mock.b]
            & mkInternalMap
            & Pattern.fromTermLike
        ]
    , becomes
        "collects \\and"
        ( mkMap
            [ (,)
                (Pattern.withCondition Mock.a ceila)
                (Pattern.withCondition Mock.b ceilb)
            ]
            []
            & fmap OrPattern.fromPattern
        )
        [ Pattern.withCondition
            (mkMapAux [(Mock.a, Mock.b)] [] [] & mkInternalMap)
            (ceila <> ceilb)
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    c = OrPattern.fromTermLike Mock.c
    ceila =
        makeCeilPredicate (Mock.f Mock.a)
            & Condition.fromPredicate
    ceilb =
        makeCeilPredicate (Mock.f Mock.b)
            & Condition.fromPredicate
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes ::
        HasCallStack =>
        TestName ->
        InternalMap Key (OrPattern RewritingVariableName) ->
        [Pattern RewritingVariableName] ->
        TestTree
    becomes name origin expect =
        testCase name $
            assertEqual
                ""
                (OrPattern.fromPatterns expect)
                (evaluate origin)

test_unparse :: [TestTree]
test_unparse =
    [ unparseTest
        "empty"
        shouldFail
        withoutUnit
        withElement
        withConcat
        $ wrapAc emptyNormalizedAc
    , unparseTest
        "empty"
        shouldSucceed
        withUnit
        withoutElement
        withoutConcat
        $ wrapAc emptyNormalizedAc
    , unparseTest
        "one element"
        shouldFail
        withUnit
        withoutElement
        withConcat
        $ builtinAcChild $ mkMapAux [(Mock.a, Mock.b)] [] []
    , unparseTest
        "one element"
        shouldSucceed
        withoutUnit
        withElement
        withoutConcat
        $ builtinAcChild $ mkMapAux [(Mock.a, Mock.b)] [] []
    , unparseTest
        "two elements"
        shouldFail
        withUnit
        withElement
        withoutConcat
        $ builtinAcChild $ mkMapAux [(Mock.a, Mock.b), (Mock.c, Mock.d)] [] []
    , unparseTest
        "two elements"
        shouldSucceed
        withoutUnit
        withElement
        withConcat
        $ builtinAcChild $ mkMapAux [(Mock.a, Mock.b), (Mock.c, Mock.d)] [] []
    , unparseTest
        "two opaque elements"
        shouldFail
        withUnit
        withElement
        withoutConcat
        $ builtinAcChild $ mkMapAux [] [] [Mock.a, Mock.b]
    , unparseTest
        "two opaque elements"
        shouldSucceed
        withoutUnit
        withoutElement
        withConcat
        $ builtinAcChild $ mkMapAux [] [] [Mock.a, Mock.b]
    ]
  where
    unparseTest ::
        String ->
        Bool ->
        Bool ->
        Bool ->
        Bool ->
        NormalizedMap Key (TermLike VariableName) ->
        TestTree
    unparseTest testName expectSuccess hasUnit hasElement hasConcat child =
        testCase fullTestName $
            if expectSuccess
                then void (Exception.evaluate $ force $ show unparsedMap)
                else
                    assertErrorIO
                        (void . return)
                        (Exception.evaluate $ force $ show unparsedMap)
      where
        (unitText, mockUnitSymbol) =
            if hasUnit
                then (" withUnit", toUnit Mock.unitMapSymbol)
                else (" withoutUnit", Unit Nothing)
        (elementText, mockElementSymbol) =
            if hasElement
                then (" withElement", toElement Mock.elementMapSymbol)
                else (" withoutElement", Element Nothing)
        (concatText, mockConcatSymbol) =
            if hasConcat
                then (" withConcat", toConcat Mock.concatMapSymbol)
                else (" withoutConcat", Concat Nothing)
        unparsedMap =
            unparse @(InternalMap Key (TermLike VariableName)) $
                InternalAc
                    { builtinAcSort = Mock.mapSort
                    , builtinAcUnit = mockUnitSymbol
                    , builtinAcElement = mockElementSymbol
                    , builtinAcConcat = mockConcatSymbol
                    , builtinAcChild = child
                    }
        fullTestName =
            "unparsing map"
                ++ unitText
                ++ elementText
                ++ concatText
                ++ " and child: "
                ++ testName

mkMap :: [(child, child)] -> [child] -> InternalMap Key child
mkMap = mkMapAux []

mkMapAux ::
    [(TermLike Concrete, child)] ->
    [(child, child)] ->
    [child] ->
    InternalMap Key child
mkMapAux concreteElements elements opaque =
    InternalAc
        { builtinAcSort = Mock.mapSort
        , builtinAcUnit = toUnit Mock.unitMapSymbol
        , builtinAcElement = toElement Mock.elementMapSymbol
        , builtinAcConcat = toConcat Mock.concatMapSymbol
        , builtinAcChild =
            NormalizedMap
                NormalizedAc
                    { elementsWithVariables = MapElement <$> elements
                    , concreteElements =
                        concreteElements
                            & map (bimap (retractKey >>> fromJust) MapValue)
                            & Map.fromList
                    , opaque
                    }
        }

evaluate ::
    InternalMap Key (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify
