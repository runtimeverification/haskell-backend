module Test.Kore.Step.Simplification.Builtin
    ( test_simplify
    ) where

import Test.Tasty

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified GHC.Stack as GHC

import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.Builtin
    ( simplify
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testGroup "List"
        [ becomes "\\bottom element" (mkList [bottom]) []
        ]
    , testGroup "Map"
        [ becomes "\\bottom value" (mkMap [(a, bottom)] []) []
        , becomes "\\bottom key" (mkMap [(bottom, a)] []) []
        , becomes "\\bottom term" (mkMap [(a, b)] [bottom]) []
        , becomes "duplicate key" (mkMap [(a, b), (a, c)] []) []
        ]
    , testGroup "Set"
        [ becomes "\\bottom element" (mkSet [bottom] []) []
        , becomes "\\bottom term" (mkSet [] [bottom]) []
        , becomes "duplicate key" (mkSet [a, a] []) []
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    c = OrPattern.fromTermLike Mock.c
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes
        :: GHC.HasCallStack
        => TestName
        -> Builtin (OrPattern Variable)
        -> [Pattern Variable]
        -> TestTree
    becomes name origin expect =
        testCase name
        $ assertEqual ""
            (OrPattern.fromPatterns expect)
            (evaluate origin)

mkMap :: [(child, child)] -> [child] -> Builtin (child)
mkMap elements opaque =
    Domain.BuiltinMap Domain.InternalAc
        { builtinAcSort = Mock.mapSort
        , builtinAcUnit = Mock.unitMapSymbol
        , builtinAcElement = Mock.elementMapSymbol
        , builtinAcConcat = Mock.concatMapSymbol
        , builtinAcChild = Domain.NormalizedMap Domain.NormalizedAc
            { elementsWithVariables = Domain.MapElement <$> elements
            , concreteElements = Map.empty
            , opaque
            }
        }

mkSet :: [child] -> [child] -> Builtin (child)
mkSet elements opaque =
    Domain.BuiltinSet Domain.InternalAc
        { builtinAcSort = Mock.setSort
        , builtinAcUnit = Mock.unitSetSymbol
        , builtinAcElement = Mock.elementSetSymbol
        , builtinAcConcat = Mock.concatSetSymbol
        , builtinAcChild = Domain.NormalizedSet Domain.NormalizedAc
            { elementsWithVariables = Domain.SetElement <$> elements
            , concreteElements = Map.empty
            , opaque
            }
        }

mkList :: [child] -> Builtin child
mkList children =
    Domain.BuiltinList Domain.InternalList
        { builtinListSort = Mock.listSort
        , builtinListUnit = Mock.unitListSymbol
        , builtinListElement = Mock.elementListSymbol
        , builtinListConcat = Mock.concatListSymbol
        , builtinListChild = Seq.fromList children
        }

evaluate :: Builtin (OrPattern Variable) -> OrPattern Variable
evaluate = simplify
