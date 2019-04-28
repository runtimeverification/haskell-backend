module Test.Kore.Step.Simplification.Top
    ( test_topSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Pure
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Simplification.Top
                 ( simplify )

import Test.Kore.Comparators ()
import Test.Kore.Step.MockSymbols
       ( testSort )
import Test.Tasty.HUnit.Extensions

test_topSimplification :: [TestTree]
test_topSimplification =
    [ testCase "Top evaluates to top"
        (assertEqualWithExplanation ""
            (MultiOr.make
                [ Pattern.top ]
            )
            (evaluate
                Top {topSort = testSort}
            )
        )
    ]

evaluate
    ::  ( MetaOrObject level)
    => Top level (OrPattern Object Variable)
    -> OrPattern Object Variable
evaluate top =
    case simplify top of
        (result, _proof) -> result
