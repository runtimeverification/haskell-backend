module Test.Kore.Step.Simplification.TermLike
    ( test_simplifyInternal
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Monad
                 ( void )
import qualified Data.Map as Map

import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.TermLike
import           Kore.Logger.Output
                 ( emptyLogger )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.TermLike as TermLike
import qualified SMT

import qualified Test.Kore.Step.MockSymbols as Mock

test_simplifyInternal :: [TestTree]
test_simplifyInternal =
    [ testCase "Evaluated" $ void
      $ simplifyInternalEvaluated $ mkEvaluated $ Mock.f Mock.a
    ]

simplifyInternalEvaluated :: TermLike Variable -> IO (OrPattern Variable)
simplifyInternalEvaluated original =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier
    $ TermLike.simplifyInternal
        Mock.metadataTools
        undefined  -- Throw an error if any predicate would be simplified.
        undefined  -- Throw an error if any term would be simplified.
        axiomSimplifiers
        original
  where
    axiomSimplifiers = Map.empty
