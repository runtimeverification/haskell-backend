module Test.Kore.Step.Simplification.Builtin
    ( test_simplify
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq

import qualified Kore.Domain.Builtin as Domain
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.Builtin
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplify :: [TestTree]
test_simplify =
    [ testCase "\\bottom propagates through builtin Map"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (OrPattern.fromPatterns [])
            (evaluate
                (mkMapDomainValue [(Mock.aConcrete, bottom)])
            )
        )
    , testCase "\\bottom propagates through builtin List"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (OrPattern.fromPatterns [])
            (evaluate
                (mkListDomainValue [bottom])
            )
        )
    ]
  where
    bottom = OrPattern.fromPatterns [Pattern.bottom]

mkMapDomainValue
    :: [(TermLike Concrete, child)]
    -> Builtin child
mkMapDomainValue children =
    Domain.BuiltinMap Domain.InternalMap
        { builtinMapSort = Mock.mapSort
        , builtinMapUnit = Mock.unitMapSymbol
        , builtinMapElement = Mock.elementMapSymbol
        , builtinMapConcat = Mock.concatMapSymbol
        , builtinMapChild = Map.fromList children
        }

mkListDomainValue :: [child] -> Builtin child
mkListDomainValue children =
    Domain.BuiltinList Domain.InternalList
        { builtinListSort = Mock.listSort
        , builtinListUnit = Mock.unitListSymbol
        , builtinListElement = Mock.elementListSymbol
        , builtinListConcat = Mock.concatListSymbol
        , builtinListChild = Seq.fromList children
        }

evaluate :: Builtin (OrPattern Variable) -> OrPattern Variable
evaluate = simplify
