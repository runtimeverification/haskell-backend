module Test.Kore.Strategies.Goal
    ( test_removalPatterns
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
import Kore.Internal.TermLike
import Kore.Strategies.Goal
    ( removalPatterns
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_removalPatterns :: [TestTree]
test_removalPatterns =
    [ testCase "user-defined \\ceil condition from unification" $ testSimplifier $ do
        let
            configuration =
                Pattern.withCondition
                    (Mock.f (mkElemVar Mock.x))
                    (Condition.fromPredicate
                        $ makeCeilPredicate Mock.testSort
                        $ Mock.f (mkElemVar Mock.x)
                    )
            destination = Pattern.fromTermLike (mkElemVar Mock.y)
            existentials = [Mock.y]

        _output <- removalPatterns destination configuration existentials

        return ()
    ]

testSimplifier :: SimplifierT NoSMT a -> IO a
testSimplifier = runSimplifierNoSMT Mock.env
