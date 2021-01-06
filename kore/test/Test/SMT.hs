module Test.SMT
    ( testPropertyWithSolver
    , testPropertyWithoutSolver
    , testCaseWithoutSMT
    , assertEqual'
    , runSMT
    , runSMTWithConfig
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
    testProperty str . Hedgehog.property . Morph.hoist (runSMT (pure ()))

testPropertyWithoutSolver
    :: HasCallStack
    => String
    -> PropertyT NoSMT ()
    -> TestTree
testPropertyWithoutSolver str =
    testProperty str . Hedgehog.property . Morph.hoist runNoSMT

testCaseWithoutSMT :: String -> NoSMT () -> TestTree
testCaseWithoutSMT str = testCase str . runNoSMT

assertEqual'
    :: MonadIO m
    => (Eq a, Show a)
    => HasCallStack
    => String  -- ^ Remark
    -> a  -- ^ Expected value
    -> a  -- ^ Actual value
    -> m ()
assertEqual' str expect = liftIO . assertEqual str expect

runSMT :: SMT () -> SMT a -> IO a
runSMT = runSMTWithConfig SMT.defaultConfig

runSMTWithConfig :: SMT.Config -> SMT () -> SMT a -> IO a
runSMTWithConfig config userInit = flip runLoggerT mempty . SMT.runSMT config userInit

runNoSMT :: NoSMT a -> IO a
runNoSMT = flip runLoggerT mempty . SMT.runNoSMT
