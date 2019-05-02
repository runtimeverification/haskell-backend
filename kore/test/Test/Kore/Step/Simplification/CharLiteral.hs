module Test.Kore.Step.Simplification.CharLiteral
    ( test_charLiteralSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Valid
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Simplification.CharLiteral
                 ( simplify )
import           Kore.Syntax

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

evaluate :: CharLiteral -> OrPattern Variable
evaluate = simplify
