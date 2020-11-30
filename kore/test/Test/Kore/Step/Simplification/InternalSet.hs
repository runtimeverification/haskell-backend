module Test.Kore.Step.Simplification.InternalSet
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Data.Map.Strict as Map

import Kore.Internal.InternalSet
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.InternalSet
    ( simplify
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testGroup "Set"
        [ becomes "\\bottom element" (mkSet [bottom] []) []
        , becomes "\\bottom term" (mkSet [] [bottom]) []
        , becomes "duplicate key" (mkSet [a, a] []) []
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes
        :: HasCallStack
        => TestName
        -> InternalSet (TermLike Concrete) (OrPattern VariableName)
        -> [Pattern VariableName]
        -> TestTree
    becomes name origin expect =
        testCase name
        $ assertEqual ""
            (OrPattern.fromPatterns expect)
            (evaluate origin)

mkSet :: [child] -> [child] -> InternalSet (TermLike Concrete) child
mkSet elements opaque =
    InternalAc
        { builtinAcSort = Mock.setSort
        , builtinAcUnit = Mock.unitSetSymbol
        , builtinAcElement = Mock.elementSetSymbol
        , builtinAcConcat = Mock.concatSetSymbol
        , builtinAcChild = NormalizedSet NormalizedAc
            { elementsWithVariables = SetElement <$> elements
            , concreteElements = Map.empty
            , opaque
            }
        }

evaluate
    :: InternalSet (TermLike Concrete) (OrPattern VariableName)
    -> OrPattern VariableName
evaluate = simplify
