module Test.Kore.Step.Simplification.DomainValue
    ( test_simplify
    ) where

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.DomainValue
    ( simplify
    )

import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqual ""
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
