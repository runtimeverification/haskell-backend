module Test.Kore.Step.Simplification.Top
    ( test_topSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Pure
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
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
            (OrOfExpandedPattern.make
                [ ExpandedPattern.top ]
            )
            (evaluate
                Top {topSort = testSort}
            )
        )
    ]

evaluate
    ::  ( MetaOrObject level)
    => Top level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate top =
    case simplify top of
        (result, _proof) -> result
