module Test.Kore.Simplify.DomainValue (
    test_simplify,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.DomainValue (
    simplify,
 )
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols (
    testSort,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ testCase
        "DomainValue evaluates to DomainValue"
        ( assertEqual
            ""
            ( OrPattern.fromTermLike $
                mkDomainValue
                    DomainValue
                        { domainValueSort = testSort
                        , domainValueChild = mkStringLiteral "a"
                        }
            )
            ( evaluate
                DomainValue
                    { domainValueSort = testSort
                    , domainValueChild =
                        OrPattern.fromTermLike $ mkStringLiteral "a"
                    }
            )
        )
    ]

evaluate ::
    DomainValue Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify
