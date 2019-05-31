module Test.Kore.Step.Simplification.DomainValue
    ( test_simplify
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.DomainValue
                 ( simplify )

import Test.Kore.Comparators ()
import Test.Kore.Step.MockSymbols
       ( testSort )
import Test.Tasty.HUnit.Extensions

test_simplify :: [TestTree]
test_simplify =
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqualWithExplanation ""
            (OrPattern.fromTermLike $ mkDomainValue
                DomainValue
                    { domainValueSort = testSort
                    , domainValueChild = mkStringLiteral "a"
                    }
            )
            (evaluate DomainValue
                { domainValueSort = testSort
                , domainValueChild =
                    OrPattern.fromTermLike $ mkStringLiteral "a"
                }
            )
        )
    ]

evaluate :: DomainValue Sort (OrPattern Variable) -> OrPattern Variable
evaluate = simplify
