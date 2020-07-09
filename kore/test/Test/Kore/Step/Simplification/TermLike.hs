module Test.Kore.Step.Simplification.TermLike
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad
    ( void
    )

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.TermLike as TermLike

import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

test_simplify :: [TestTree]
test_simplify =
    [ testCase "Evaluated" $ void
      $ simplifyEvaluated $ mkEvaluated $ Mock.f Mock.a
    ]

simplifyEvaluated :: TermLike VariableName -> IO (OrPattern VariableName)
simplifyEvaluated original =
    runSimplifier env $ TermLike.simplify SideCondition.top original
  where
    env = Mock.env
        { simplifierTermLike =
            -- Throw an error if any term would be simplified.
            termLikeSimplifier $ const undefined
        , simplifierCondition =
            -- Throw an error if any predicate would be simplified.
            ConditionSimplifier $ const undefined
        }
