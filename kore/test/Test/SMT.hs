module Test.SMT where

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import           Control.Monad.IO.Class
import qualified Control.Monad.Morph as Morph

import           SMT
                 ( SMT )
import qualified SMT

testPropertyWithSolver :: String -> PropertyT SMT () -> TestTree
testPropertyWithSolver str =
    testProperty str . Hedgehog.property . Morph.hoist runSMT

testCaseWithSMT :: String -> SMT () -> TestTree
testCaseWithSMT str = testCase str . runSMT

assertEqual' :: MonadIO m => Eq a => Show a => String -> a -> a -> m ()
assertEqual' str expect = liftIO . assertEqual str expect

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig mempty
