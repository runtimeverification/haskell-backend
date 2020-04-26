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
import Kore.Rewriting.RewritingVariable
import qualified Kore.Step.Remainder as Remainder
import Kore.Variables.Target

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Terse

test_existentiallyQuantifyTarget :: [TestTree]
test_existentiallyQuantifyTarget =
    [ target `becomes` quantified $  "quantifies target variables"
    ]
  where
    becomes original expect =
        equals (Remainder.existentiallyQuantifyRuleVariables original) expect

target :: Predicate RewritingVariable
target =
    Predicate.makeEqualsPredicate_
        (mkElemVar . fmap RewritingVariable $ mkElementNonTarget Mock.x)
        (Mock.sigma
            (mkElemVar . fmap RewritingVariable $ mkElementTarget Mock.y)
            (mkElemVar . fmap RewritingVariable $ mkElementTarget Mock.z)
        )

quantified :: Predicate RewritingVariable
quantified =
    Predicate.makeMultipleExists
        [ RewritingVariable <$> mkElementTarget Mock.y
        , RewritingVariable <$> mkElementTarget Mock.z
        ]
        target
