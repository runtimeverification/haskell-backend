module Test.Kore.Simplify.Bottom (
    test_bottomSimplification,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern qualified as Pattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Bottom (
    simplify,
 )
import Kore.Sort
import Kore.Syntax.Bottom
import Prelude.Kore ()
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase
        "Bottom evaluates to bottom"
        ( assertEqual
            ""
            (OrPattern.fromPatterns [Pattern.bottomOf Mock.testSort])
            (evaluate Bottom{bottomSort = Mock.testSort})
        )
    ]

evaluate ::
    Bottom Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify
