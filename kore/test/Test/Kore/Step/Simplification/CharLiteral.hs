module Test.Kore.Step.Simplification.CharLiteral
    ( test_charLiteralSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.CharLiteral
                 ( simplify )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_charLiteralSimplification :: [TestTree]
test_charLiteralSimplification =
    [ testCase "CharLiteral evaluates to CharLiteral"
        (assertEqualWithExplanation ""
            (OrPattern.fromTermLike $ mkCharLiteral 'a')
            (evaluate (CharLiteral 'a'))
        )
    ]

evaluate :: CharLiteral (OrPattern Variable) -> OrPattern Variable
evaluate = simplify
