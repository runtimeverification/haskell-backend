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
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Data.Map.Strict as StrictMap
import qualified Kore.Builtin.Int as Int
import           Kore.Internal.TermLike
                 ( TermLike, mkApp, mkBottom_, mkVar, varS )
import qualified Kore.Logger.Output as Logger
import           Kore.OnePath.Verification
                 ( Axiom (..), verifyClaimStep )
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Step.Rule
                 ( OnePathRule (..), RewriteRule (..), rulePattern )

import           Kore.Step.Simplification.AndTerms
                 ( cannotUnifyDistinctDomainValues )
import           Kore.Step.Simplification.Data
                 ( Simplifier, evalSimplifier )
import           Kore.Syntax.Variable
                 ( Variable )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Unification.Unify
                 ( explainBottom )
import qualified SMT

import Test.Kore
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition

type Claim = OnePathRule Variable

test_replInterpreter :: [TestTree]
test_replInterpreter =
    [ showUsage              `tests` "Showing the usage message"
    , help                   `tests` "Showing the help message"
    , step5                  `tests` "Performing 5 steps"
    , step100                `tests` "Stepping over proof completion"
    , makeSimpleAlias        `tests` "Creating an alias with no arguments"
    , trySimpleAlias         `tests` "Executing an existing alias with no arguments"
    , makeAlias              `tests` "Creating an alias with arguments"
    , aliasOfExistingCommand `tests` "Create alias of existing command"
    , aliasOfUnknownCommand  `tests` "Create alias of unknown command"
    , recursiveAlias         `tests` "Create alias of unknown command"
    , tryAlias               `tests` "Executing an existing alias with arguments"
    , unificationFailure     `tests` "Force axiom that doesn't unify"
    , proofStatus            `tests` "Multi claim proof status"
    , logUpdatesState        `tests` "Log command updates the state"
    ]

showUsage :: IO ()
showUsage =
    let
        axioms  = []
        claim   = emptyClaim
        command = ShowUsage
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` showUsageMessage
        continue `equals`       True

help :: IO ()
help =
    let
        axioms  = []
        claim   = emptyClaim
        command = Help
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` helpText
        continue `equals`       True

step5 :: IO ()
step5 =
    let
        axioms = [ add1 ]
        claim  = zeroToTen
        command = ProveSteps 5
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
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
        Result { output, continue, state } <- run command axioms [claim] claim
        output     `equalsOutput`   showStepStoppedMessage 10 NoResult
        continue   `equals`         True
        state      `hasCurrentNode` ReplNode 10

makeSimpleAlias :: IO ()
makeSimpleAlias =
    let
        axioms  = []
        claim   = emptyClaim
        alias   = AliasDefinition { name = "a", arguments = [], command = "help" }
        command = Alias alias
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        output   `equalsOutput` ""
        continue `equals`       True
        state    `hasAlias`     alias

trySimpleAlias :: IO ()
trySimpleAlias =
    let
        axioms  = []
        claim   = emptyClaim
        name    = "h"
        alias   = AliasDefinition { name, arguments = [], command = "help" }
        stateT  = \st -> st { aliases = Map.insert name alias (aliases st) }
        command = TryAlias $ ReplAlias "h" []
    in do
        Result { output, continue } <-
            runWithState command axioms [claim] claim stateT
        output   `equalsOutput` helpText
        continue `equals` True

makeAlias :: IO ()
makeAlias =
    let
        axioms  = []
        claim   = emptyClaim
        alias   = AliasDefinition
                    { name = "c"
                    , arguments = ["n"]
                    , command = "claim n"
                    }
        command = Alias alias
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        output   `equalsOutput` ""
        continue `equals`       True
        state    `hasAlias`     alias

aliasOfExistingCommand :: IO ()
aliasOfExistingCommand =
    let
        axioms  = []
        claim   = emptyClaim
        alias   = AliasDefinition
                    { name = "help"
                    , arguments = ["n"]
                    , command = "claim n"
                    }
        command = Alias alias
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` showAliasError NameAlreadyDefined
        continue `equals`       True

aliasOfUnknownCommand :: IO ()
aliasOfUnknownCommand =
    let
        axioms  = []
        claim   = emptyClaim
        alias   = AliasDefinition
                    { name = "c"
                    , arguments = ["n"]
                    , command = "unknown n"
                    }
        command = Alias alias
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` showAliasError UnknownCommand
        continue `equals`       True

recursiveAlias :: IO ()
recursiveAlias =
    let
        axioms  = []
        claim   = emptyClaim
        alias   = AliasDefinition
                    { name = "c"
                    , arguments = ["n"]
                    , command = "c n"
                    }
        command = Alias alias
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` showAliasError UnknownCommand
        continue `equals`       True

tryAlias :: IO ()
tryAlias =
    let
        axioms  = []
        claim   = emptyClaim
        name    = "c"
        alias   = AliasDefinition
                    { name = "c"
                    , arguments = ["n"]
                    , command = "claim n"
                    }
        stateT  = \st -> st { aliases = Map.insert name alias (aliases st) }
        command = TryAlias $ ReplAlias "c" [SimpleArgument "0"]
    in do
        Result { output, continue } <-
            runWithState command axioms [claim] claim stateT
        output   `equalsOutput` showRewriteRule claim
        continue `equals` True

unificationFailure :: IO ()
unificationFailure =
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = coerce $ rulePattern one one
        axioms = [ impossibleAxiom ]
        claim = zeroToTen
        command = Try . Left $ AxiomIndex 0
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        expectedOutput <-
            unificationErrorMessage cannotUnifyDistinctDomainValues one zero
        output `equalsOutput` expectedOutput
        continue `equals` True
        state `hasCurrentNode` ReplNode 0

proofStatus :: IO ()
proofStatus =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        command = ProofStatus
        expectedProofStatus =
            StrictMap.fromList
                [ (ClaimIndex 0, InProgress [0])
                , (ClaimIndex 1, NotStarted)
                ]
    in do
        Result { output, continue } <-
            run command axioms claims claim
        output `equalsOutput` showProofStatus expectedProofStatus
        continue `equals` True

logUpdatesState :: IO ()
logUpdatesState =
    let
        axioms  = []
        claim   = emptyClaim
        command = Log Logger.Info LogToStdOut
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        output   `equalsOutput`  ""
        continue `equals`     True
        state    `hasLogging` (Logger.Info, LogToStdOut)

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

run :: ReplCommand -> [Axiom] -> [Claim] -> Claim -> IO Result
run command axioms claims claim =
    runWithState command axioms claims claim id

runSimplifier
    :: Simplifier a
    -> IO a
runSimplifier =
    SMT.runSMT SMT.defaultConfig emptyLogger . evalSimplifier

runWithState
    :: ReplCommand
    -> [Axiom]
    -> [Claim]
    -> Claim
    -> (ReplState Claim -> ReplState Claim)
    -> IO Result
runWithState command axioms claims claim stateTransformer
  = Logger.withLogger logOptions $ \logger -> do
        output <- newIORef ""
        (c, s) <- liftSimplifier logger
            $ replInterpreter (writeIORefIfNotEmpty output) command
                `runStateT` state
        output' <- readIORef output
        return $ Result output' c s
  where
    logOptions = Logger.KoreLogOptions Logger.LogNone Logger.Debug
    liftSimplifier logger =
        SMT.runSMT SMT.defaultConfig logger . evalSimplifier
    state = stateTransformer $ mkState axioms claims claim
    writeIORefIfNotEmpty out =
        \case
            "" -> pure ()
            xs -> writeIORef out xs

data Result = Result
    { output   :: String
    , continue :: Bool
    , state    :: ReplState Claim
    }

equals :: (Eq a, Show a) => a -> a -> Assertion
equals = (@?=)

equalsOutput :: String -> String -> Assertion
equalsOutput "" expected     = "" @?= expected
equalsOutput actual expected = actual @?= expected <> "\n"

hasCurrentNode :: ReplState Claim -> ReplNode -> IO ()
hasCurrentNode st n = do
    node st `equals` n
    graphNode <- evalStateT (getTargetNode justNode) st
    graphNode `equals` justNode
  where
    justNode = Just n

hasAlias :: ReplState Claim -> AliasDefinition -> IO ()
hasAlias st alias@AliasDefinition { name } =
    let
        aliasMap = aliases st
        actual   = name `Map.lookup` aliasMap
    in
        actual `equals` Just alias

hasLogging :: ReplState Claim -> (Logger.Severity, LogType) -> IO ()
hasLogging st expectedLogging =
    let
        actualLogging = logging st
    in
        actualLogging `equals` expectedLogging

tests :: IO () -> String -> TestTree
tests = flip testCase

mkState :: [Axiom] -> [Claim] -> Claim -> ReplState Claim
mkState axioms claims claim =
    ReplState
        { axioms      = axioms
        , claims      = claims
        , claim       = claim
        , claimIndex  = ClaimIndex 0
        , graphs      = Map.singleton (ClaimIndex 0) graph'
        , node        = ReplNode 0
        , commands    = Seq.empty
        , omit        = []
        , stepper     = stepper0
        , unifier     = unifier0
        , labels      = Map.singleton (ClaimIndex 0) Map.empty
        , aliases     = Map.empty
        , logging     = (Logger.Debug, NoLogging)
        }
  where
    graph' = emptyExecutionGraph claim
    stepper0 claim' claims' axioms' graph (ReplNode node) =
        verifyClaimStep
            testMetadataTools
            testTermLikeSimplifier
            testSubstitutionSimplifier
            testEvaluators
            claim'
            claims'
            axioms'
            graph
            node
    unifier0
        :: TermLike Variable
        -> TermLike Variable
        -> UnifierWithExplanation ()
    unifier0 first second =
        () <$ unificationProcedure
            testMetadataTools
            testSubstitutionSimplifier
            testTermLikeSimplifier
            testEvaluators
            first
            second

unificationErrorMessage
    :: Pretty.Doc ()
    -> TermLike Variable
    -> TermLike Variable
    -> IO String
unificationErrorMessage info first second = do
    res <- runSimplifier . runUnifierWithExplanation
        $ explainBottom info first second
    return $ formatUnificationMessage res
