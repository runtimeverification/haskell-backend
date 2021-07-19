module Test.Kore.Simplify.StringLiteral (
    test_stringLiteralSimplification,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Conditional (..),
 )
import Kore.Internal.Predicate (
    makeTruePredicate,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.StringLiteral (
    simplify,
 )
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_stringLiteralSimplification :: [TestTree]
test_stringLiteralSimplification =
    [ testCase
        "StringLiteral evaluates to StringLiteral"
        ( assertEqual
            ""
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = mkStringLiteral "a"
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            ( evaluate
                (StringLiteral "a")
            )
        )
    ]

evaluate :: StringLiteral -> OrPattern RewritingVariableName
evaluate = simplify
