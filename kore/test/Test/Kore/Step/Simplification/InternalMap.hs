module Test.Kore.Step.Simplification.InternalMap
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Data.Map.Strict as Map

import Kore.Internal.Conditional
    ( Conditional (..)
    )
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
    ( makeTruePredicate_
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.InternalMap
    ( simplify
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testGroup "Map"
        [ becomes "\\bottom value" (mkMap [(a, bottom)] []) []
        , becomes "\\bottom key" (mkMap [(bottom, a)] []) []
        , becomes "\\bottom term" (mkMap [(a, b)] [bottom]) []
        , becomes "duplicate key" (mkMap [(a, b), (a, c)] []) []
        , becomes "single opaque elem" (mkMap [] [a]) [aPat]
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    c = OrPattern.fromTermLike Mock.c
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    aPat =
        Conditional
            { term = Mock.a
            , predicate = makeTruePredicate_
            , substitution = mempty
            }
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
