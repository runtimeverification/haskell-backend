module Test.Kore.Step.Simplification.Bottom
    ( test_bottomSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Bottom (..) )
import           Kore.AST.MetaOrObject
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Bottom
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase "Bottom evaluates to bottom"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern.bottom ]
            )
            (evaluate
                Bottom {bottomSort = Mock.testSort}
            )
        )
    ]

evaluate
    ::  ( MetaOrObject level)
    => Bottom level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate bottom =
    case simplify bottom of
        (result, _proof) -> result
