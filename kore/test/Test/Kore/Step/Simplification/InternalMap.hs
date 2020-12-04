module Test.Kore.Step.Simplification.InternalMap
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Data.Map.Strict as Map

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
    ( makeCeilPredicate_
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.InternalMap
    ( simplify
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
        [ mkMap [(Mock.a, Mock.c)] [] & mkBuiltinMap & Pattern.fromTermLike
        , mkMap [(Mock.b, Mock.c)] [] & mkBuiltinMap & Pattern.fromTermLike
        ]
    , becomes "distributes \\or value" (mkMap [(a, b <> c)] [])
        [ mkMap [(Mock.a, Mock.b)] [] & mkBuiltinMap & Pattern.fromTermLike
        , mkMap [(Mock.a, Mock.c)] [] & mkBuiltinMap & Pattern.fromTermLike
        ]
    , becomes "distributes \\or compound" (mkMap [] [a <> b])
        [ mkMap [] [Mock.a] & mkBuiltinMap & Pattern.fromTermLike
        , mkMap [] [Mock.b] & mkBuiltinMap & Pattern.fromTermLike
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
            (mkMap [(Mock.a, Mock.b)] [] & mkBuiltinMap)
            (ceila <> ceilb)
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    c = OrPattern.fromTermLike Mock.c
    ceila =
        makeCeilPredicate_ (Mock.f Mock.a)
        & Condition.fromPredicate
    ceilb =
        makeCeilPredicate_ (Mock.f Mock.b)
        & Condition.fromPredicate
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes
        :: HasCallStack
        => TestName
        -> InternalMap (TermLike Concrete) (OrPattern VariableName)
        -> [Pattern VariableName]
        -> TestTree
    becomes name origin expect =
        testCase name
        $ assertEqual ""
            (OrPattern.fromPatterns expect)
            (evaluate origin)

mkMap :: [(child, child)] -> [child] -> InternalMap (TermLike Concrete) child
mkMap elements opaque =
    InternalAc
        { builtinAcSort = Mock.mapSort
        , builtinAcUnit = Mock.unitMapSymbol
        , builtinAcElement = Mock.elementMapSymbol
        , builtinAcConcat = Mock.concatMapSymbol
        , builtinAcChild = NormalizedMap NormalizedAc
            { elementsWithVariables = MapElement <$> elements
            , concreteElements = Map.empty
            , opaque
            }
        }

evaluate
    :: InternalMap (TermLike Concrete) (OrPattern VariableName)
    -> OrPattern VariableName
evaluate = simplify
