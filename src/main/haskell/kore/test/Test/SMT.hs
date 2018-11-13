module Test.SMT where

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import           Control.Concurrent.MVar
import           Control.Monad.IO.Class
                 ( liftIO )
import qualified Control.Monad.Morph as Morph
import           Control.Monad.Reader
                 ( runReaderT )
import           GHC.Stack
                 ( HasCallStack )

import           SMT
                 ( SMT, Solver )
import qualified SMT

propertyWithSolver
    :: HasCallStack
    => PropertyT SMT ()
    -> IO (MVar Solver)
    -> Property
propertyWithSolver within getMVar = Hedgehog.property $ do
    mvar <- liftIO getMVar
    Morph.hoist (\smt -> runReaderT (SMT.getSMT smt) mvar) within

testPropertyWithSolver
    :: HasCallStack
    => TestName
    -> PropertyT SMT ()
    -> TestTree
testPropertyWithSolver name propt =
    withSolver (testProperty name . propertyWithSolver propt)

testCaseWithSolver
    :: HasCallStack
    => TestName
    -> (MVar Solver -> Assertion)
    -> TestTree
testCaseWithSolver name within =
    withSolver $ \getMVar -> testCase name (getMVar >>= within)

withSolver :: (IO (MVar Solver) -> TestTree) -> TestTree
withSolver = withResource new free
  where
    new = SMT.newSolver SMT.defaultConfig
    free = SMT.stopSolver
