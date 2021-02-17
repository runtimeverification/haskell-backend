module Test.Kore.Step.Simplification.Bottom
    ( test_bottomSimplification
    ) where

import Prelude.Kore ()

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
    ( bottom
    )
import Kore.Sort
import Kore.Step.Simplification.Bottom
    ( simplify
    )
import Kore.Syntax.Bottom

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext
import Kore.Rewriting.RewritingVariable (RewritingVariableName)

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase "Bottom evaluates to bottom"
        (assertEqual ""
            (OrPattern.fromPatterns [ Pattern.bottom ])
            (evaluate Bottom { bottomSort = Mock.testSort })
        )
    ]

evaluate
    :: Bottom Sort (OrPattern RewritingVariableName)
    -> OrPattern RewritingVariableName
evaluate = simplify
