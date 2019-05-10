module Test.Kore.Repl.Interpreter
    ( test_replInterpreter
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( Assertion, testCase, (@?=) )

import           Control.Monad.Trans.State.Strict
                 ( evalStateT, runStateT )
import           Data.Coerce
                 ( coerce )
import           Data.IORef
                 ( newIORef, readIORef, writeIORef )
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import qualified Kore.Builtin.Int as Int
import           Kore.Internal.TermLike
                 ( mkApp, mkBottom_, mkVar, varS )
import           Kore.OnePath.Verification
                 ( Axiom (..), verifyClaimStep )
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Step.Rule
                 ( OnePathRule (..), RewriteRule (..), rulePattern )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Syntax.Variable
                 ( Variable )
import qualified SMT

import Test.Kore
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition

type Claim = OnePathRule Variable

test_replInterpreter :: [TestTree]
test_replInterpreter =
    [ showUsage `tests` "Showing the usage message"
    , help      `tests` "Showing the help message"
    , step5     `tests` "Performing 5 steps"
    , step100   `tests` "Stepping over proof completion"
    ]

showUsage :: IO ()
showUsage =
    let
        axioms  = []
        claim   = emptyClaim
        command = ShowUsage
    in do
        Result { output, continue } <- run command axioms claim
        output   `equalsOutput` showUsageMessage
        continue `equals`       True

help :: IO ()
help =
    let
        axioms  = []
        claim   = emptyClaim
        command = Help
    in do
        Result { output, continue } <- run command axioms claim
        output   `equalsOutput` helpText
        continue `equals`       True

step5 :: IO ()
step5 =
    let
        axioms = [ add1 ]
        claim  = zeroToTen
        command = ProveSteps 5
    in do
        Result { output, continue, state } <- run command axioms claim
        output     `equalsOutput`   ""
        continue   `equals`         True
        state      `hasCurrentNode` ReplNode 5

step100 :: IO ()
step100 =
    let
        axioms = [ add1 ]
        claim  = zeroToTen
        command = ProveSteps 100
    in do
        Result { output, continue, state } <- run command axioms claim
        output     `equalsOutput`   showStepStoppedMessage 10 NoResult
        continue   `equals`         True
        state      `hasCurrentNode` ReplNode 10

add1 :: Axiom
add1 = coerce $ rulePattern n plusOne
  where
    one     = Int.asInternal intSort 1
    n       = mkVar $ varS "x" intSort
    plusOne = mkApp intSort addIntSymbol [n, one]

zeroToTen :: Claim
zeroToTen = coerce $ rulePattern zero ten
  where
    zero = Int.asInternal intSort 0
    ten  = Int.asInternal intSort 10

emptyClaim :: Claim
emptyClaim = coerce $ rulePattern mkBottom_ mkBottom_

run :: ReplCommand -> [Axiom] -> Claim -> IO Result
run command axioms claim =  do
    output <- newIORef ""
    (c, s) <- liftSimplifier $
        replInterpreter (writeIORef output) command `runStateT` state
    output' <- readIORef output
    return $ Result output' c s
  where
    liftSimplifier = SMT.runSMT SMT.defaultConfig . evalSimplifier emptyLogger
    state = mkState axioms claim

data Result = Result
    { output   :: String
    , continue :: Bool
    , state    :: ReplState Claim
    }

equals
    :: (Eq a, Show a)
    => a
    -> a
    -> Assertion
equals = (@?=)

equalsOutput
    :: String
    -> String
    -> Assertion
equalsOutput "" expected     = "" @?= expected
equalsOutput actual expected = actual @?= expected <> "\n"

hasCurrentNode :: ReplState Claim -> ReplNode -> IO ()
hasCurrentNode st n = do
    node st `equals` n
    graphNode <- evalStateT (getTargetNode justNode) st
    graphNode `equals` justNode
  where
    justNode = Just n

tests :: IO () -> String -> TestTree
tests = flip testCase

mkState :: [Axiom] -> Claim -> ReplState Claim
mkState axioms claim =
    ReplState
        { axioms   = axioms
        , claims   = [claim]
        , claim    = claim
        , graph    = graph'
        , node     = ReplNode 0
        , commands = Seq.empty
        , omit     = []
        , stepper  = stepper0
        , unifier  = unifier0
        , labels   = Map.empty
        , aliases  = Map.empty
        }
  where
    graph' = emptyExecutionGraph claim
    stepper0 claim' claims' axioms' graph (ReplNode node) =
        verifyClaimStep
            testMetadataTools
            smtSimplifier
            testSubstitutionSimplifier
            evaluators
            claim'
            claims'
            axioms'
            graph
            node
    unifier0 _ _ = return ()
