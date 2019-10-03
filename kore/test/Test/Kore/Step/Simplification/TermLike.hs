module Test.Kore.Step.Simplification.TermLike
    ( test_simplifyInternal
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad
    ( void
    )

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Predicate as Predicate
    ( top
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.TermLike as TermLike

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

test_simplifyInternal :: [TestTree]
test_simplifyInternal =
    [ testCase "Evaluated" $ void
      $ simplifyInternalEvaluated $ mkEvaluated $ Mock.f Mock.a
    ]

simplifyInternalEvaluated :: TermLike Variable -> IO (OrPattern Variable)
simplifyInternalEvaluated original =
    runSimplifier env $ TermLike.simplifyInternal original Predicate.top
  where
    env = Mock.env
        { simplifierTermLike =
            -- Throw an error if any term would be simplified.
            termLikeSimplifier $ const undefined
        , simplifierPredicate =
            -- Throw an error if any predicate would be simplified.
            PredicateSimplifier $ const undefined
        }
