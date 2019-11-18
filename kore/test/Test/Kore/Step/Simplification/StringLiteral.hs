module Test.Kore.Step.Simplification.StringLiteral
    ( --t-est_stringLiteralSimplification
    ) where
{-
import Test.Tasty

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.Predicate
    ( makeTruePredicate
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.StringLiteral
    ( simplify
    )

import Test.Tasty.HUnit.Ext

t-est_stringLiteralSimplification :: [TestTree]
t-est_stringLiteralSimplification =
    [ testCase "StringLiteral evaluates to StringLiteral"
        (assertEqual ""
            Conditional
                    { term = mkStringLiteral "a"
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            (evaluate
                (StringLiteral "a")
            )
        )
    ]

evaluate :: StringLiteral -> Pattern Variable
evaluate = simplify
-}
