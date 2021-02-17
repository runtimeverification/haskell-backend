{-# LANGUAGE Strict #-}

module Test.Kore.Step.Simplification.InternalMap
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty

import Data.Bifunctor
    ( bimap
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( fromJust
    )

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalMap
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeCeilPredicate
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.InternalMap
    ( simplify
    )

import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ becomes "\\bottom value" (mkMap [(a, bottom)] []) []
    , becomes "\\bottom key" (mkMap [(bottom, a)] []) []
    , becomes "\\bottom term" (mkMap [(a, b)] [bottom]) []
    , becomes "duplicate key" (mkMap [(a, b), (a, c)] []) []
    , becomes "single opaque elem" (mkMap [] [a])
        [Mock.a & Pattern.fromTermLike]
    , becomes "distributes \\or key" (mkMap [(a <> b, c)] [])
        [ mkMapAux [(Mock.a, Mock.c)] [] []
            & mkInternalMap & Pattern.fromTermLike
        , mkMapAux [(Mock.b, Mock.c)] [] []
            & mkInternalMap & Pattern.fromTermLike
        ]
    , becomes "distributes \\or value" (mkMap [(a, b <> c)] [])
        [ mkMapAux [(Mock.a, Mock.b)] [] []
            & mkInternalMap & Pattern.fromTermLike
        , mkMapAux [(Mock.a, Mock.c)] [] []
            & mkInternalMap & Pattern.fromTermLike
        ]
    , becomes "distributes \\or compound" (mkMap [(a, b)] [a <> b])
        [ mkMapAux [(Mock.a, Mock.b)] [] [Mock.a]
            & mkInternalMap & Pattern.fromTermLike
        , mkMapAux [(Mock.a, Mock.b)] [] [Mock.b]
            & mkInternalMap & Pattern.fromTermLike
        ]
    , becomes "collects \\and"
        (mkMap
            [ (,)
                (Pattern.withCondition Mock.a ceila)
                (Pattern.withCondition Mock.b ceilb)
            ]
            []
            & fmap OrPattern.fromPattern
        )
        [Pattern.withCondition
            (mkMapAux [(Mock.a, Mock.b)] [] [] & mkInternalMap)
            (ceila <> ceilb)
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    c = OrPattern.fromTermLike Mock.c
    ceila =
        makeCeilPredicate(Mock.f Mock.a)
        & Condition.fromPredicate
    ceilb =
        makeCeilPredicate (Mock.f Mock.b)
        & Condition.fromPredicate
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes
        :: HasCallStack
        => TestName
        -> InternalMap Key (OrPattern RewritingVariableName)
        -> [Pattern RewritingVariableName]
        -> TestTree
    becomes name origin expect =
        testCase name
        $ assertEqual ""
            (OrPattern.fromPatterns expect)
            (evaluate origin)

mkMap :: [(child, child)] -> [child] -> InternalMap Key child
mkMap = mkMapAux []

mkMapAux
    :: [(TermLike Concrete, child)]
    -> [(child, child)]
    -> [child]
    -> InternalMap Key child
mkMapAux concreteElements elements opaque =
    InternalAc
        { builtinAcSort = Mock.mapSort
        , builtinAcUnit = Mock.unitMapSymbol
        , builtinAcElement = Mock.elementMapSymbol
        , builtinAcConcat = Mock.concatMapSymbol
        , builtinAcChild = NormalizedMap NormalizedAc
            { elementsWithVariables = MapElement <$> elements
            , concreteElements =
                concreteElements
                & map (bimap (retractKey >>> fromJust) MapValue)
                & Map.fromList
            , opaque
            }
        }

evaluate
    :: InternalMap Key (OrPattern RewritingVariableName)
    -> OrPattern RewritingVariableName
evaluate = simplify
