module Test.Kore.Step.Simplification.Top
    ( test_topSimplification
    ) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( testCase
    )

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Step.Simplification.Top
    ( simplify
    )
import Kore.Syntax

import Test.Kore.Comparators ()
import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Extensions

test_topSimplification :: [TestTree]
test_topSimplification =
    [ testCase "Top evaluates to top"
        (assertEqualWithExplanation ""
            (OrPattern.fromPattern Pattern.top)
            (evaluate Top { topSort = testSort })
        )
    ]

evaluate :: Top Sort (OrPattern Variable) -> OrPattern Variable
evaluate = simplify
