module Test.Kore.Step.Simplification.Bottom
    ( test_bottomSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Bottom (..), Sort (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.Predicate.Predicate
                 ( makeFalsePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Bottom
                 ( simplify )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_bottomSimplification :: [TestTree]
test_bottomSimplification =
    [ testCase "Bottom evaluates to bottom"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkBottom
                    , predicate = makeFalsePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                Bottom {bottomSort = testSort}
            )
        )
    ]

testSort :: Sort Object
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level)
    => Bottom level (CommonOrOfExpandedPattern level domain)
    -> CommonOrOfExpandedPattern level domain
evaluate bottom =
    case simplify bottom of
        (result, _proof) -> result
