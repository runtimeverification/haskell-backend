module Test.Kore.Step.Remainder where

import Test.Tasty

import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Remainder as Remainder
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Variables.Target
    ( Target (..)
    )

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
    Predicate.makeEqualsPredicate
        (mkElemVar $ NonTarget <$> Mock.x)
        (Mock.sigma
            (mkElemVar $ Target <$> Mock.y)
            (mkElemVar $ Target <$> Mock.z)
        )

quantified :: Predicate (Target Variable)
quantified =
    Predicate.makeMultipleExists
        [Target <$> Mock.y, Target <$> Mock.z]
        target
