module Test.Kore.Step.Simplification.CharLiteral
    ( test_charLiteralSimplification
    ) where

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.CharLiteral
    ( simplify
    )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Ext

test_charLiteralSimplification :: [TestTree]
test_charLiteralSimplification =
    [ testCase "CharLiteral evaluates to CharLiteral"
        (assertEqual ""
            (OrPattern.fromTermLike $ mkCharLiteral 'a')
            (evaluate (CharLiteral 'a'))
        )
    ]

evaluate :: CharLiteral -> OrPattern Variable
evaluate = simplify
