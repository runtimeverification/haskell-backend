{-# LANGUAGE Strict #-}

module Test.SMT (
    testPropertyWithSolver,
    testPropertyWithoutSolver,
    testCaseWithoutSMT,
    assertEqual',
    runSMT,
    runSMTWithConfig,
    runNoSMT,
) where

import qualified Control.Monad.Morph as Morph
import Hedgehog
import Log (
    runLoggerT,
 )
import Prelude.Kore
import SMT (
    NoSMT,
    SMT,
 )
import qualified SMT
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

testPropertyWithSolver ::
    HasCallStack =>
    String ->
    PropertyT SMT () ->
    TestTree
testPropertyWithSolver str =
    testProperty str . Hedgehog.property . Morph.hoist (runSMT (pure ()))

testPropertyWithoutSolver ::
    HasCallStack =>
    String ->
    PropertyT NoSMT () ->
    TestTree
testPropertyWithoutSolver str =
    testProperty str . Hedgehog.property . Morph.hoist runNoSMT

testCaseWithoutSMT :: String -> NoSMT () -> TestTree
testCaseWithoutSMT str = testCase str . runNoSMT

assertEqual' ::
    MonadIO m =>
    (Eq a, Show a) =>
    HasCallStack =>
    -- | Remark
    String ->
    -- | Expected value
    a ->
    -- | Actual value
    a ->
    m ()
assertEqual' str expect = liftIO . assertEqual str expect

runSMT :: SMT () -> SMT a -> IO a
runSMT = runSMTWithConfig SMT.defaultConfig

runSMTWithConfig :: SMT.Config -> SMT () -> SMT a -> IO a
runSMTWithConfig config userInit = flip runLoggerT mempty . SMT.runSMT config userInit

runNoSMT :: NoSMT a -> IO a
runNoSMT = flip runLoggerT mempty . SMT.runNoSMT
