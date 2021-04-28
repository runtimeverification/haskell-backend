module Test.Kore.Step.Simplification.Bottom (
    test_bottomSimplification,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern (
    bottom,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Sort
import Kore.Step.Simplification.Bottom (
    simplify,
 )
import Kore.Syntax.Bottom
import Prelude.Kore ()
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase
        "Bottom evaluates to bottom"
        ( assertEqual
            ""
            (OrPattern.fromPatterns [Pattern.bottom])
            (evaluate Bottom{bottomSort = Mock.testSort})
        )
    ]

evaluate ::
    Bottom Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify
