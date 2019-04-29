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
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import qualified Kore.Step.Pattern as Pattern
                 ( bottom )
import           Kore.Step.Simplification.Bottom
                 ( simplify )
import           Kore.Syntax.Variable
                 ( Variable (..) )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase "Bottom evaluates to bottom"
        (assertEqualWithExplanation ""
            (OrPattern.fromPatterns
                [ Pattern.bottom ]
            )
            (evaluate
                Bottom {bottomSort = Mock.testSort}
            )
        )
    ]

evaluate
    :: Bottom Object (OrPattern Object Variable)
    -> OrPattern Object Variable
evaluate bottom =
    case simplify bottom of
        (result, _proof) -> result
