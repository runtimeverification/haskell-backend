{-# LANGUAGE Strict #-}
module Test.Kore.Step.Simplification.TermLike
    ( test_simplify
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad
    ( void
    )
import Control.Monad.Catch
    ( MonadThrow
    )

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import qualified Kore.Step.Function.Memo as Memo
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.TermLike as TermLike
import qualified Logic

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

simplifyEvaluated :: TermLike RewritingVariableName -> IO (OrPattern RewritingVariableName)
simplifyEvaluated original =
    runSimplifier env . getTestSimplifier
    $ TermLike.simplify SideCondition.top original
  where
    env = Mock.env
        { simplifierCondition =
            -- Throw an error if any predicate would be simplified.
            ConditionSimplifier $ const undefined
        }

newtype TestSimplifier a =
    TestSimplifier { getTestSimplifier :: SimplifierT NoSMT a }
    deriving newtype (Functor, Applicative, Monad)
    deriving newtype (MonadLog, MonadSMT, MonadThrow)

instance MonadSimplify TestSimplifier where
    askMetadataTools = TestSimplifier askMetadataTools
    askSimplifierAxioms = TestSimplifier askSimplifierAxioms
    localSimplifierAxioms f =
        TestSimplifier . localSimplifierAxioms f . getTestSimplifier
    askMemo = TestSimplifier (Memo.liftSelf TestSimplifier <$> askMemo)
    askInjSimplifier = TestSimplifier askInjSimplifier
    askOverloadSimplifier = TestSimplifier askOverloadSimplifier
    simplifyCondition sideCondition condition =
        Logic.mapLogicT TestSimplifier
        (simplifyCondition sideCondition condition)

    -- Throw an error if any term would be simplified.
    simplifyTermLike = undefined
