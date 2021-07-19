module Test.Kore.Rewrite.Remainder (
    test_existentiallyQuantifyTarget,
) where

import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Rewrite.Remainder as Remainder
import Kore.Rewrite.RewritingVariable
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
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
