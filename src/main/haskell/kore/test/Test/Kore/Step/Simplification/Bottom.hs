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
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( bottom )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import           Kore.Step.Simplification.Bottom
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase "Bottom evaluates to bottom"
        (assertEqualWithExplanation ""
            (MultiOr.make
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
