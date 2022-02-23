module Test.Kore.Rewrite.Remainder (
    test_existentiallyQuantifyTarget,
) where

import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.TermLike
import Kore.Rewrite.Remainder qualified as Remainder
import Kore.Rewrite.RewritingVariable
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Tasty
import Test.Terse

test_existentiallyQuantifyTarget :: [TestTree]
test_existentiallyQuantifyTarget =
    [ target `becomes` quantified $ "quantifies target variables"
    ]
  where
    becomes original expect =
        equals (Remainder.existentiallyQuantifyRuleVariables original) expect

target :: Predicate RewritingVariableName
target =
    Predicate.makeEqualsPredicate
        (mkElemVar $ mkElementConfigVariable Mock.x)
        ( Mock.sigma
            (mkElemVar $ mkElementRuleVariable Mock.y)
            (mkElemVar $ mkElementRuleVariable Mock.z)
        )

quantified :: Predicate RewritingVariableName
quantified =
    Predicate.makeMultipleExists
        [ mkElementRuleVariable Mock.y
        , mkElementRuleVariable Mock.z
        ]
        target
