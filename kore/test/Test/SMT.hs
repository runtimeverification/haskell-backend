module Test.SMT
    ( testPropertyWithSolver
    , testPropertyWithoutSolver
    , testCaseWithSMT
    , assertEqual'
    , runSMT
    , runNoSMT
    ) where

import Prelude.Kore

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import qualified Control.Monad.Morph as Morph

import Log
    ( runLoggerT
    )
import SMT
    ( NoSMT
    , SMT
    )
import qualified SMT

testPropertyWithSolver
    :: HasCallStack
    => String
    -> PropertyT SMT ()
    -> TestTree
testPropertyWithSolver str =
    testProperty str . Hedgehog.property . Morph.hoist runSMT

testPropertyWithoutSolver
    :: HasCallStack
    => String
    -> PropertyT NoSMT ()
    -> TestTree
testPropertyWithoutSolver str =
    testProperty str . Hedgehog.property . Morph.hoist runNoSMT

testCaseWithSMT :: String -> SMT () -> TestTree
testCaseWithSMT str = testCase str . runSMT

assertEqual'
    :: MonadIO m
    => (Eq a, Show a)
    => HasCallStack
    => String  -- ^ Remark
    -> a  -- ^ Expected value
    -> a  -- ^ Actual value
    -> m ()
assertEqual' str expect = liftIO . assertEqual str expect

runSMT :: SMT a -> IO a
runSMT = flip runLoggerT mempty . SMT.runSMT SMT.defaultConfig

runNoSMT :: NoSMT a -> IO a
runNoSMT = flip runLoggerT mempty . SMT.runNoSMT
