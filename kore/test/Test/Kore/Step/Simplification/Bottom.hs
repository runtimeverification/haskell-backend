module Test.Kore.Step.Simplification.Bottom
    ( test_bottomSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Bottom (..), Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.Pattern as Pattern
                 ( bottom )
import qualified Kore.Step.Representation.MultiOr as MultiOr
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
            (MultiOr.make
                [ Pattern.bottom ]
            )
            (evaluate
                Bottom {bottomSort = Mock.testSort}
            )
        )
    ]

evaluate
    ::  ( MetaOrObject level)
    => Bottom level (OrPattern level Variable)
    -> OrPattern level Variable
evaluate bottom =
    case simplify bottom of
        (result, _proof) -> result
