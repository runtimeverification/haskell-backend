module Test.SMT where

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import           Control.Monad.IO.Class
import qualified Control.Monad.Morph as Morph

import SMT

testPropertyWithSolver :: String -> PropertyT SMT () -> TestTree
testPropertyWithSolver str =
    testProperty str
        . Hedgehog.property
        . Morph.hoist (runSMT defaultConfig mempty)

testCaseWithSMT :: String -> SMT () -> TestTree
testCaseWithSMT str =
    testCase str
        . runSMT defaultConfig mempty

assertEqual' :: MonadIO m => Eq a => Show a => String -> a -> a -> m ()
assertEqual' str expect = liftIO . assertEqual str expect
