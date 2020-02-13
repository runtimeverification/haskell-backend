module Test.Kore.Step.Remainder
    ( test_existentiallyQuantifyTarget
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Step.Remainder as Remainder
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Variables.Target

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Terse

test_existentiallyQuantifyTarget :: [TestTree]
test_existentiallyQuantifyTarget =
    [ target `becomes` quantified $  "quantifies target variables"
    ]
  where
    becomes original expect =
        equals (Remainder.existentiallyQuantifyTarget original) expect

target :: Predicate (Target Variable)
target =
    Predicate.makeEqualsPredicate_
        (mkElemVar $ mkElementNonTarget Mock.x)
        (Mock.sigma
            (mkElemVar $ mkElementTarget Mock.y)
            (mkElemVar $ mkElementTarget Mock.z)
        )

quantified :: Predicate (Target Variable)
quantified =
    Predicate.makeMultipleExists
        [mkElementTarget Mock.y, mkElementTarget Mock.z]
        target
