module Test.Kore.Repl.Interpreter
    ( test_replInterpreter
    ) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( Assertion
    , testCase
    , (@?=)
    )

import Control.Applicative
import Control.Concurrent.MVar
import qualified Control.Lens as Lens
import Control.Monad.Reader
    ( runReaderT
    )
import Control.Monad.Trans.State.Strict
    ( evalStateT
    , runStateT
    )
import Data.Coerce
    ( coerce
    )
import Data.Function
import Data.Generics.Product
import Data.IORef
    ( IORef
    , modifyIORef
    , newIORef
    , readIORef
    )
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.Text
    ( pack
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Data.Map.Strict as StrictMap
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Builtin.Int as Int
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , elemVarS
    , mkBottom_
    , mkElemVar
    )
import qualified Kore.Logger.Output as Logger
import Kore.Repl.Data
import Kore.Repl.Interpreter
import Kore.Repl.State
import Kore.Step.Rule
import Kore.Step.Simplification.AndTerms
    ( cannotUnifyDistinctDomainValues
    )
import qualified Kore.Step.Simplification.Data as Kore
import Kore.Strategies.Goal
import Kore.Strategies.Verification
    ( verifyClaimStep
    )
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Unification.Procedure
    ( unificationProcedure
    )
import Kore.Unification.Unify
    ( explainBottom
    )
import qualified SMT

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Step.Simplification

type Claim = OnePathRule Variable
type Axiom = Rule (OnePathRule Variable)

test_replInterpreter :: [TestTree]
test_replInterpreter =
    [ showUsage                   `tests` "Showing the usage message"
    , help                        `tests` "Showing the help message"
    , step5                       `tests` "Performing 5 steps"
    , step100                     `tests` "Stepping over proof completion"
    , makeSimpleAlias             `tests` "Creating an alias with no arguments"
    , trySimpleAlias              `tests` "Executing an existing alias with no arguments"
    , makeAlias                   `tests` "Creating an alias with arguments"
    , aliasOfExistingCommand      `tests` "Create alias of existing command"
    , aliasOfUnknownCommand       `tests` "Create alias of unknown command"
    , recursiveAlias              `tests` "Create alias of unknown command"
    , tryAlias                    `tests` "Executing an existing alias with arguments"
    , unificationFailure          `tests` "Try axiom that doesn't unify"
    , unificationSuccess          `tests` "Try axiom that does unify"
    , forceFailure                `tests` "TryF axiom that doesn't unify"
    , forceSuccess                `tests` "TryF axiom that does unify"
    , proofStatus                 `tests` "Multi claim proof status"
    , logUpdatesState             `tests` "Log command updates the state"
    , showCurrentClaim            `tests` "Showing current claim"
    , showClaim1                  `tests` "Showing the claim at index 1"
    , showClaimByName             `tests` "Showing the claim with the name 0to10Claim"
    , showAxiomByName             `tests` "Showing the axiom with the name add1Axiom"
    , unificationFailureWithName  `tests` "Try axiom by name that doesn't unify"
    , unificationSuccessWithName  `tests` "Try axiom by name that does unify"
    , forceFailureWithName        `tests` "TryF axiom by name that doesn't unify"
    , forceSuccessWithName        `tests` "TryF axiom by name that does unify"
    , proveSecondClaim            `tests` "Starting to prove the second claim"
    , proveSecondClaimByName      `tests` "Starting to prove the second claim\
                                           \ referenced by name"
    ]

showUsage :: IO ()
showUsage =
    let
        axioms  = []
        claim   = emptyClaim
        command = ShowUsage
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` makeAuxReplOutput showUsageMessage
        continue `equals`       Continue

help :: IO ()
help =
    let
        axioms  = []
        claim   = emptyClaim
        command = Help
    in do
        Result { output, continue } <- run command axioms [claim] claim
        output   `equalsOutput` makeAuxReplOutput helpText
        continue `equals`       Continue

step5 :: IO ()
step5 =
    let
        axioms = [ add1 ]
        claim  = zeroToTen
        command = ProveSteps 5
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        output     `equalsOutput`   mempty
        continue   `equals`         Continue
        state      `hasCurrentNode` ReplNode 5

step100 :: IO ()
step100 =
    let
        axioms = [ add1 ]
        claim  = zeroToTen
        command = ProveSteps 100
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        let expectedOutput =
                makeAuxReplOutput $ showStepStoppedMessage 10 NoResult
        output     `equalsOutput`   expectedOutput
        continue   `equals`         Continue
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
        output   `equalsOutput` mempty
        continue `equals`       Continue
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
        output   `equalsOutput` makeAuxReplOutput helpText
        continue `equals` Continue

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
        output   `equalsOutput` mempty
        continue `equals`       Continue
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
        let expectedOutput =
                makeAuxReplOutput . showAliasError $ NameAlreadyDefined
        output   `equalsOutput` expectedOutput
        continue `equals`       Continue

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
        let expectedOutput =
                makeAuxReplOutput . showAliasError $ UnknownCommand
        output   `equalsOutput` expectedOutput
        continue `equals`       Continue

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
        let expectedOutput =
                makeAuxReplOutput . showAliasError $ UnknownCommand
        output   `equalsOutput` expectedOutput
        continue `equals`       Continue

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
        continue `equals` Continue

unificationFailure :: IO ()
unificationFailure =
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = coerce $ rulePattern one one
        axioms = [ impossibleAxiom ]
        claim = zeroToTen
        command = Try . ByIndex . Left $ AxiomIndex 0
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        expectedOutput <-
            formatUnificationError cannotUnifyDistinctDomainValues one zero
        output `equalsOutput` expectedOutput
        continue `equals` Continue
        state `hasCurrentNode` ReplNode 0

unificationFailureWithName :: IO ()
unificationFailureWithName =
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = coerce $ rulePatternWithName one one "impossible"
        axioms = [ impossibleAxiom ]
        claim = zeroToTen
        command = Try . ByName . RuleName $ "impossible"
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        expectedOutput <-
            formatUnificationError cannotUnifyDistinctDomainValues one zero
        output `equalsOutput` expectedOutput
        continue `equals` Continue
        state `hasCurrentNode` ReplNode 0

unificationSuccess :: IO ()
unificationSuccess = do
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = coerce $ rulePattern zero one
        axioms = [ axiom ]
        claim = zeroToTen
        command = Try . ByIndex . Left $ AxiomIndex 0
        expectedOutput = formatUnifiers (Predicate.top :| [])

    Result { output, continue, state } <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 0

unificationSuccessWithName :: IO ()
unificationSuccessWithName = do
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = coerce $ rulePatternWithName zero one "0to1"
        axioms = [ axiom ]
        claim = zeroToTen
        command = Try . ByName . RuleName $ "0to1"
        expectedOutput = formatUnifiers (Predicate.top :| [])

    Result { output, continue, state } <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 0

forceFailure :: IO ()
forceFailure =
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = coerce $ rulePattern one one
        axioms = [ impossibleAxiom ]
        claim = zeroToTen
        command = TryF . ByIndex . Left $ AxiomIndex 0
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        expectedOutput <-
            formatUnificationError cannotUnifyDistinctDomainValues one zero
        output `equalsOutput` expectedOutput
        continue `equals` Continue
        state `hasCurrentNode` ReplNode 0

forceFailureWithName :: IO ()
forceFailureWithName =
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = coerce $ rulePatternWithName one one "impossible"
        axioms = [ impossibleAxiom ]
        claim = zeroToTen
        command = TryF . ByName . RuleName $ "impossible"
    in do
        Result { output, continue, state } <- run command axioms [claim] claim
        expectedOutput <-
            formatUnificationError cannotUnifyDistinctDomainValues one zero
        output `equalsOutput` expectedOutput
        continue `equals` Continue
        state `hasCurrentNode` ReplNode 0

forceSuccess :: IO ()
forceSuccess = do
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = coerce $ rulePattern zero one
        axioms = [ axiom ]
        claim = zeroToTen
        command = TryF . ByIndex . Left $ AxiomIndex 0
        expectedOutput = mempty

    Result { output, continue, state } <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 1

forceSuccessWithName :: IO ()
forceSuccessWithName = do
    let
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = coerce $ rulePatternWithName zero one "0to1"
        axioms = [ axiom ]
        claim = zeroToTen
        command = TryF . ByName . RuleName $ "0to1"
        expectedOutput = mempty

    Result { output, continue, state } <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 1

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
        output `equalsOutput` makeAuxReplOutput (showProofStatus expectedProofStatus)
        continue `equals` Continue

showCurrentClaim :: IO ()
showCurrentClaim =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = []
        command = ShowClaim Nothing
        expectedCindex = ClaimIndex 0
    in do
        Result { output, continue } <-
            run command axioms claims claim
        output `equalsOutput` makeAuxReplOutput (showCurrentClaimIndex expectedCindex)
        continue `equals` Continue

showClaim1 :: IO ()
showClaim1 =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = []
        command = ShowClaim (Just . Left . ClaimIndex $ 1)
        expectedClaim = emptyClaim
    in do
        Result { output, continue } <-
            run command axioms claims claim
        output `equalsOutput` showRewriteRule expectedClaim
        continue `equals` Continue

showClaimByName :: IO ()
showClaimByName =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = []
        command = ShowClaim (Just . Right . RuleName $ "0to10Claim")
        expectedClaim = zeroToTen
    in do
        Result { output, continue } <-
            run command axioms claims claim
        output `equalsOutput` showRewriteRule expectedClaim
        continue `equals` Continue

showAxiomByName :: IO ()
showAxiomByName =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        command = ShowAxiom (Right . RuleName $ "add1Axiom")
        expectedAxiom = add1
    in do
        Result { output, continue } <-
            run command axioms claims claim
        output `equalsOutput` showRewriteRule expectedAxiom
        continue `equals` Continue

logUpdatesState :: IO ()
logUpdatesState =
    let
        axioms  = []
        claim   = emptyClaim
        command =
            Log Logger.Info (makeLogScope ["scope1", "scope2"]) LogToStdOut
    in do
        Result { output, continue, state } <-
            run command axioms [claim] claim
        output   `equalsOutput` mempty
        continue `equals`     Continue
        state
            `hasLogging`
            (Logger.Info, (makeLogScope ["scope1", "scope2"]), LogToStdOut)

proveSecondClaim :: IO ()
proveSecondClaim =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        indexOrName = Left . ClaimIndex $ 1
        command = Prove indexOrName
        expectedClaimIndex = ClaimIndex 1
    in do
        Result { output, continue, state } <-
            run command axioms claims claim
        output `equalsOutput` makeAuxReplOutput (showClaimSwitch indexOrName)
        state `hasCurrentClaimIndex` expectedClaimIndex
        continue `equals` Continue

proveSecondClaimByName :: IO ()
proveSecondClaimByName =
    let
        claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        indexOrName = Right . RuleName $ "emptyClaim"
        command = Prove indexOrName
        expectedClaimIndex = ClaimIndex 1
    in do
        Result { output, continue, state } <-
            run command axioms claims claim
        output `equalsOutput` makeAuxReplOutput (showClaimSwitch indexOrName)
        state `hasCurrentClaimIndex` expectedClaimIndex
        continue `equals` Continue

add1 :: Axiom
add1 =
    coerce $ rulePatternWithName n plusOne "add1Axiom"
  where
    one     = Int.asInternal intSort 1
    n       = mkElemVar $ elemVarS "x" intSort
    plusOne = n `addInt` one

zeroToTen :: Claim
zeroToTen =
    coerce $ rulePatternWithName zero ten "0to10Claim"
  where
    zero = Int.asInternal intSort 0
    ten  = Int.asInternal intSort 10

emptyClaim :: Claim
emptyClaim =
    coerce
    $ rulePatternWithName mkBottom_ mkBottom_ "emptyClaim"

rulePatternWithName
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> String
    -> RulePattern variable
rulePatternWithName left right name =
    rulePattern left right
    & Lens.set (field @"attributes" . typed @Attribute.Label) label
  where
    label = Attribute.Label . pure $ pack name

run :: ReplCommand -> [Axiom] -> [Claim] -> Claim -> IO Result
run command axioms claims claim =
    runWithState command axioms claims claim id

runWithState
    :: ReplCommand
    -> [Axiom]
    -> [Claim]
    -> Claim
    -> (ReplState Claim -> ReplState Claim)
    -> IO Result
runWithState command axioms claims claim stateTransformer
  = Logger.withLogger logOptions $ \logger -> do
        output <- newIORef (mempty :: ReplOutput)
        mvar <- newMVar logger
        let state = stateTransformer $ mkState axioms claims claim
        let config = mkConfig mvar
        (c, s) <-
            liftSimplifier (Logger.swappableLogger mvar)
            $ flip runStateT state
            $ flip runReaderT config
            $ replInterpreter0
                (PrintAuxOutput . modifyAuxOutput $ output)
                (PrintKoreOutput . modifyKoreOutput $ output)
                command
        output' <- readIORef output
        return $ Result output' c s
  where
    logOptions = Logger.KoreLogOptions Logger.LogNone Logger.Debug mempty
    liftSimplifier logger =
        SMT.runSMT SMT.defaultConfig logger . Kore.runSimplifier testEnv

    modifyAuxOutput :: IORef ReplOutput -> String -> IO ()
    modifyAuxOutput ref s = modifyIORef ref (appReplOut . AuxOut $ s)

    modifyKoreOutput :: IORef ReplOutput -> String -> IO ()
    modifyKoreOutput ref s = modifyIORef ref (appReplOut . KoreOut $ s)

data Result = Result
    { output   :: ReplOutput
    , continue :: ReplStatus
    , state    :: ReplState Claim
    }

equals :: (Eq a, Show a) => a -> a -> Assertion
equals = (@?=)

equalsOutput :: ReplOutput -> ReplOutput -> Assertion
equalsOutput actual expected =
    actual @?= expected

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

hasLogging
    :: ReplState Claim
    -> (Logger.Severity, LogScope, LogType)
    -> IO ()
hasLogging st expectedLogging =
    let
        actualLogging = logging st
    in
        actualLogging `equals` expectedLogging

hasCurrentClaimIndex :: ReplState Claim -> ClaimIndex -> IO ()
hasCurrentClaimIndex st expectedClaimIndex =
    let
        actualClaimIndex = claimIndex st
    in
        actualClaimIndex `equals` expectedClaimIndex

tests :: IO () -> String -> TestTree
tests = flip testCase

mkState
    :: [Axiom]
    -> [Claim]
    -> Claim
    -> ReplState Claim
mkState axioms claims claim =
    ReplState
        { axioms      = axioms
        , claims      = claims
        , claim       = claim
        , claimIndex  = ClaimIndex 0
        , graphs      = Map.singleton (ClaimIndex 0) graph'
        , node        = ReplNode 0
        , commands    = Seq.empty
        , omit        = mempty
        , labels      = Map.singleton (ClaimIndex 0) Map.empty
        , aliases     = Map.empty
        , logging     = (Logger.Debug, mempty, NoLogging)
        }
  where
    graph' = emptyExecutionGraph claim

mkConfig
    :: MVar (Logger.LogAction IO Logger.SomeEntry)
    -> Config Claim Simplifier
mkConfig logger =
    Config
        { stepper     = stepper0
        , unifier     = unificationProcedure
        , logger
        , outputFile  = OutputFile Nothing
        }
  where
    stepper0
        :: Claim
        -> [Claim]
        -> [Axiom]
        -> ExecutionGraph Axiom
        -> ReplNode
        -> Simplifier (ExecutionGraph Axiom)
    stepper0 claim' claims' axioms' graph (ReplNode node) =
        verifyClaimStep claim' claims' axioms' graph node

formatUnificationError
    :: Pretty.Doc ()
    -> TermLike Variable
    -> TermLike Variable
    -> IO ReplOutput
formatUnificationError info first second = do
    res <- runSimplifier testEnv . runUnifierWithExplanation $ do
        explainBottom info first second
        empty
    return $ formatUnificationMessage res

formatUnifiers :: NonEmpty (Predicate Variable) -> ReplOutput
formatUnifiers = formatUnificationMessage . Right
