module Test.Kore.Step.Simplification.CharLiteral
    ( test_charLiteralSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( CharLiteral (..), KoreDomain )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkCharLiteral )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.CharLiteral
                 ( simplify )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_charLiteralSimplification :: [TestTree]
test_charLiteralSimplification =
    [ testCase "CharLiteral evaluates to CharLiteral"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkCharLiteral (CharLiteral 'a')
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (CharLiteral 'a')
            )
        )
    ]

evaluate
    ::  ( MetaOrObject Meta)
    => CharLiteral
    -> CommonOrOfExpandedPattern Meta KoreDomain
evaluate charLiteral =
    case simplify charLiteral of
        (result, _proof) -> result
