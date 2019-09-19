module Test.Kore.Step.Simplification
    ( Simplifier, Env (..)
    , runSimplifier
    , runSimplifierBranch
    ) where

import Branch
    ( BranchT
    )
import Kore.Step.Simplification.Data
    ( Env (..)
    , Simplifier
    )
import qualified Kore.Step.Simplification.Data as Kore

import qualified Test.SMT as Test

runSimplifier :: Env Simplifier -> Simplifier a -> IO a
runSimplifier env = Test.runSMT . Kore.runSimplifier env

runSimplifierBranch :: Env Simplifier -> BranchT Simplifier a -> IO [a]
runSimplifierBranch env = Test.runSMT . Kore.runSimplifierBranch env
