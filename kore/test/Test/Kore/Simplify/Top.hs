module Test.Kore.Simplify.Top (
    test_topSimplification,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern qualified as Pattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Top (
    simplify,
 )
import Kore.Syntax
import Prelude.Kore ()
import Test.Kore.Rewrite.MockSymbols (
    testSort,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_topSimplification :: [TestTree]
test_topSimplification =
    [ testCase
        "Top evaluates to top"
        ( assertEqual
            ""
            (OrPattern.fromPattern (Pattern.topOf testSort))
            (evaluate Top{topSort = testSort})
        )
    ]

evaluate ::
    Top Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify
