module Test.Kore.Step.Simplification.Builtin
    ( test_simplify
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified GHC.Stack as GHC

import qualified Kore.Domain.Builtin as Domain
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern ( Pattern)
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.Builtin
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplify :: [TestTree]
test_simplify =
    [ becomes "\\bottom value becomes \\bottom Map" (mkMap [(a, bottom)] []) []
    , becomes "\\bottom key becomes \\bottom Map" (mkMap [(bottom, a)] []) []
    , becomes "\\bottom term becomes \\bottom Map" (mkMap [(a, b)] [bottom]) []
    , becomes "\\bottom element becomes \\bottom List" (mkList [bottom]) []
    , becomes "\\bottom element becomes \\bottom Set" (mkSet [bottom] []) []
    , becomes "\\bottom term becomes \\bottom Set" (mkSet [] [bottom]) []
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes
        :: GHC.HasCallStack
        => TestName
        -> Builtin (OrPattern Variable)
        -> [Pattern Variable]
        -> TestTree
    becomes name origin expect =
        testCase name
        $ assertEqualWithExplanation ""
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
