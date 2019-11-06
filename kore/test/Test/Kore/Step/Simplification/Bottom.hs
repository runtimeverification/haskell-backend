module Test.Kore.Step.Simplification.Bottom
    ( test_bottomSimplification
    ) where

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( bottom
    )
import Kore.Sort
import Kore.Step.Simplification.Bottom
    ( simplify
    )
import Kore.Syntax.Bottom
import Kore.Syntax.Variable

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase "Bottom evaluates to bottom"
        (assertEqual ""
            Pattern.bottom
            (evaluate Bottom { bottomSort = Mock.testSort })
        )
    ]

evaluate :: Bottom Sort (OrPattern Variable) -> Pattern Variable
evaluate = simplify
