module Test.Kore.Step.Simplification.Top
    ( test_topSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Pure
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Top
                 ( simplify )

import Test.Kore.Comparators ()
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

testSort :: Sort Object
testSort =
    case mkTop :: CommonStepPattern Object of
        Top_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level)
    => Top level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate top =
    case simplify top of
        (result, _proof) -> result
