{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Test.Kore.Rewrite.Remainder (
    test_existentiallyQuantifyTarget,
) where

import Data.List (sort)
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.TermLike
import Kore.Rewrite.Remainder qualified as Remainder
import Kore.Rewrite.RewritingVariable
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols (MockElementVariable)
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

[x, y, z] :: [MockElementVariable] = sort [Mock.x, Mock.y, Mock.z]

target :: Predicate RewritingVariableName
target =
    Predicate.makeEqualsPredicate
        (mkElemVar $ mkElementConfigVariable x)
        ( Mock.sigma
            (mkElemVar $ mkElementRuleVariable y)
            (mkElemVar $ mkElementRuleVariable z)
        )

quantified :: Predicate RewritingVariableName
quantified =
    Predicate.makeMultipleExists
        [ mkElementRuleVariable y
        , mkElementRuleVariable z
        ]
        target
