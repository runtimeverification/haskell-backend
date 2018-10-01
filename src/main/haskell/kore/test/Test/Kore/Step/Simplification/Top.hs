module Test.Kore.Step.Simplification.Top
    ( test_topSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Sort (..), Top (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
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
    case mkTop of
        Top_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level)
    => Top level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate top =
    case simplify top of
        (result, _proof) -> result
