module Test.Kore.Step.Simplification.CharLiteral
    ( test_charLiteralSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
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
                [ Predicated
                    { term = mkCharLiteral 'a'
                    , predicate = makeTruePredicate
                    , substitution = mempty
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
    -> CommonOrOfExpandedPattern Meta
evaluate charLiteral =
    case simplify charLiteral of
        (result, _proof) -> result
