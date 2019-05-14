module Test.Kore.Step.Simplification.DomainValue
    ( test_simplify
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Kore.Domain.Builtin as Domain
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.TermLike
import           Kore.Step.Simplification.DomainValue
                 ( simplify )

import           Test.Kore.Comparators ()
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplify :: [TestTree]
test_simplify =
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqualWithExplanation ""
            (OrPattern.fromTermLike $ mkDomainValue
                Domain.External
                    { domainValueSort = testSort
                    , domainValueChild = mkStringLiteral "a"
                    }
            )
            (evaluate Domain.External
                { domainValueSort = testSort
                , domainValueChild =
                    OrPattern.fromTermLike $ mkStringLiteral "a"
                }
            )
        )
    ]

evaluate
    :: Domain.External (OrPattern Variable)
    -> OrPattern Variable
evaluate = simplify Mock.emptyMetadataTools
