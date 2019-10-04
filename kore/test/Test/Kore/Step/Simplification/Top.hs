module Test.Kore.Step.Simplification.Top
    ( test_topSimplification
    ) where

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Step.Simplification.Top
    ( simplify
    )
import Kore.Syntax

import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Ext

test_topSimplification :: [TestTree]
test_topSimplification =
    [ testCase "Top evaluates to top"
        (assertEqual ""
            (OrPattern.fromPattern Pattern.top)
            (evaluate Top { topSort = testSort })
        )
    ]

evaluate :: Top Sort (OrPattern Variable) -> OrPattern Variable
evaluate = simplify
