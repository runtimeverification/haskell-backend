-- no head/tail warnings
{-# OPTIONS_GHC -Wno-x-partial #-}

module Test.Kore.Repl.Interpreter (
    test_replInterpreter,
) where

import Control.Concurrent.MVar
import Control.Lens qualified as Lens
import Control.Monad.Reader (
    runReaderT,
 )
import Control.Monad.Trans.State.Strict (
    evalStateT,
    runStateT,
 )
import Data.Coerce (
    coerce,
 )
import Data.Generics.Product
import Data.HashSet qualified as HashSet
import Data.IORef (
    IORef,
    modifyIORef,
    newIORef,
    readIORef,
 )
import Data.Map.Strict qualified as Map
import Data.Map.Strict qualified as StrictMap
import Data.Sequence qualified as Seq
import Data.Text (
    pack,
 )
import Kore.Attribute.Axiom qualified as Attribute
import Kore.Attribute.Definition
import Kore.Builtin.Int qualified as Int
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike (
    TermLike,
    mkBottom,
    mkElemVar,
 )
import Kore.Log qualified as Log
import Kore.Log.DebugUnifyBottom (
    DebugUnifyBottom (..),
    mkDebugUnifyBottom,
 )
import Kore.Log.Registry qualified as Log
import Kore.Reachability hiding (
    AppliedRule,
 )
import Kore.Repl.Data
import Kore.Repl.Interpreter
import Kore.Repl.State
import Kore.Rewrite.ClaimPattern (
    ClaimPattern,
    mkClaimPattern,
 )
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    rulePattern,
 )
import Kore.Rewrite.Timeout (
    EnableMovingAverage (..),
    StepMovingAverage,
    StepTimeout (..),
 )
import Kore.Simplify.Simplify qualified as Kore
import Kore.Syntax.Module (
    ModuleName (..),
 )
import Kore.Unification.Procedure (
    unificationProcedure,
 )
import Kore.Unparser (
    unparseToString,
 )
import Prelude.Kore
import SMT qualified
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    getTime,
 )
import System.Console.Haskeline (
    defaultSettings,
    runInputT,
 )
import Test.Kore (
    runTestLoggerT,
 )
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Simplify
import Test.Tasty (
    DependencyType (AllFinish),
    TestTree,
    after_,
    testGroup,
 )
import Test.Tasty.HUnit (
    Assertion,
    testCase,
    (@?=),
 )
import Test.Tasty.Patterns.Types as T (Expr (..))

runSequentially :: [(String, IO ())] -> [TestTree]
runSequentially tests
    | null tests = []
    | otherwise = foldr before [testCase (withNum 0 lastName) lastTest] $ init tests
  where
    (lastName, lastTest) = last tests
    total = length tests
    withNum n s = show (total - n) <> " - " <> s

    before :: (String, IO ()) -> [TestTree] -> [TestTree]
    (name, t) `before` [] =
        [testCase (withNum total name) t]
    (name, t) `before` (next : rest) =
        let name' = withNum (length rest + 1) name
         in testCase name' t
                : after_ AllFinish (T.EQ (Field NF) (StringLit name')) next
                : rest

test_replInterpreter :: TestTree
test_replInterpreter =
    testGroup "Interpreter interaction" . runSequentially $
        -- we need to sequentialise these tests, `runInputT` in
        -- `runWithState` is not thread-safe
        [ showUsage `tests` "Showing the usage message"
        , help `tests` "Showing the help message"
        , step5 `tests` "Performing 5 steps"
        , step100 `tests` "Stepping over proof completion"
        , stepf5noBranching `tests` "Performing 5 foced steps in non-branching proof"
        , stepf100noBranching `tests` "Stepping over proof completion"
        , makeSimpleAlias `tests` "Creating an alias with no arguments"
        , trySimpleAlias `tests` "Executing an existing alias with no arguments"
        , makeAlias `tests` "Creating an alias with arguments"
        , aliasOfExistingCommand `tests` "Create alias of existing command"
        , aliasOfUnknownCommand `tests` "Create alias of unknown command"
        , recursiveAlias `tests` "Create alias of unknown command"
        , tryAlias `tests` "Executing an existing alias with arguments"
        , unificationFailure `tests` "Try axiom that doesn't unify"
        , unificationSuccess `tests` "Try axiom that does unify"
        , forceFailure `tests` "TryF axiom that doesn't unify"
        , forceSuccess `tests` "TryF axiom that does unify"
        , tryResultsInProven `tests` "TryF axiom results in proven config"
        , proofStatus `tests` "Multi claim proof status"
        , logUpdatesState `tests` "Log command updates the state"
        , debugAttemptEquationUpdatesState `tests` "DebugAttemptEquation command updates the state"
        , debugApplyEquationUpdatesState `tests` "DebugApplyEquation command updates the state"
        , debugEquationUpdatesState `tests` "DebugEquation command updates the state"
        , showCurrentClaim `tests` "Showing current claim"
        , showClaim1 `tests` "Showing the claim at index 1"
        , showClaimByName `tests` "Showing the claim with the name 0to10Claim"
        , showAxiomByName `tests` "Showing the axiom with the name add1Axiom"
        , unificationFailureWithName `tests` "Try axiom by name that doesn't unify"
        , unificationSuccessWithName `tests` "Try axiom by name that does unify"
        , forceFailureWithName `tests` "TryF axiom by name that doesn't unify"
        , forceSuccessWithName `tests` "TryF axiom by name that does unify"
        , proveSecondClaim `tests` "Starting to prove the second claim"
        , proveSecondClaimByName
            `tests` "Starting to prove the second claim\
                    \ referenced by name"
        ]
  where
    x `tests` name = (name, x)

showUsage :: IO ()
showUsage =
    let axioms = []
        claim = emptyClaim
        command = ShowUsage
     in do
            Result{output, continue} <- run command axioms [claim] claim
            output `equalsOutput` makeAuxReplOutput showUsageMessage
            continue `equals` Continue

help :: IO ()
help =
    let axioms = []
        claim = emptyClaim
        command = Help
     in do
            Result{output, continue} <- run command axioms [claim] claim
            output `equalsOutput` makeAuxReplOutput helpText
            continue `equals` Continue

step5 :: IO ()
step5 =
    let axioms = [add1]
        claim = zeroToTen
        command = ProveSteps 5
     in do
            Result{output, continue, state} <- run command axioms [claim] claim
            output `equalsOutput` mempty
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 5

step100 :: IO ()
step100 =
    let axioms = [add1]
        claim = zeroToTen
        command = ProveSteps 100
     in do
            Result{output, continue, state} <- run command axioms [claim] claim
            let expectedOutput =
                    makeAuxReplOutput $ showStepStoppedMessage 10 NoResult
            output `equalsOutput` expectedOutput
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 10

stepf5noBranching :: IO ()
stepf5noBranching =
    let axioms = [add1]
        claim = zeroToTen
        command = ProveStepsF 5
     in do
            Result{output, continue, state} <- run command axioms [claim] claim
            output `equalsOutput` mempty
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 5

stepf100noBranching :: IO ()
stepf100noBranching =
    let axioms = [add1]
        claim = zeroToTen
        command = ProveStepsF 100
     in do
            Result{output, continue, state} <- run command axioms [claim] claim
            let expectedOutput =
                    makeAuxReplOutput "Proof completed on all branches."
            output `equalsOutput` expectedOutput
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 0

makeSimpleAlias :: IO ()
makeSimpleAlias =
    let axioms = []
        claim = emptyClaim
        alias = AliasDefinition{name = "a", arguments = [], command = "help"}
        command = Alias alias
     in do
            Result{output, continue, state} <- run command axioms [claim] claim
            output `equalsOutput` mempty
            continue `equals` Continue
            state `hasAlias` alias

trySimpleAlias :: IO ()
trySimpleAlias =
    let axioms = []
        claim = emptyClaim
        name = "h"
        alias = AliasDefinition{name, arguments = [], command = "help"}
        stateT = \st -> st{aliases = Map.insert name alias (aliases st)}
        command = TryAlias $ ReplAlias "h" []
     in do
            Result{output, continue} <-
                runWithState command axioms [claim] claim stateT
            output `equalsOutput` makeAuxReplOutput helpText
            continue `equals` Continue

makeAlias :: IO ()
makeAlias =
    let axioms = []
        claim = emptyClaim
        alias =
            AliasDefinition
                { name = "c"
                , arguments = ["n"]
                , command = "claim n"
                }
        command = Alias alias
     in do
            Result{output, continue, state} <- run command axioms [claim] claim
            output `equalsOutput` mempty
            continue `equals` Continue
            state `hasAlias` alias

aliasOfExistingCommand :: IO ()
aliasOfExistingCommand =
    let axioms = []
        claim = emptyClaim
        alias =
            AliasDefinition
                { name = "help"
                , arguments = ["n"]
                , command = "claim n"
                }
        command = Alias alias
     in do
            Result{output, continue} <- run command axioms [claim] claim
            let expectedOutput =
                    makeAuxReplOutput . showAliasError $ NameAlreadyDefined
            output `equalsOutput` expectedOutput
            continue `equals` Continue

aliasOfUnknownCommand :: IO ()
aliasOfUnknownCommand =
    let axioms = []
        claim = emptyClaim
        alias =
            AliasDefinition
                { name = "c"
                , arguments = ["n"]
                , command = "unknown n"
                }
        command = Alias alias
     in do
            Result{output, continue} <- run command axioms [claim] claim
            let expectedOutput =
                    makeAuxReplOutput . showAliasError $ UnknownCommand
            output `equalsOutput` expectedOutput
            continue `equals` Continue

recursiveAlias :: IO ()
recursiveAlias =
    let axioms = []
        claim = emptyClaim
        alias =
            AliasDefinition
                { name = "c"
                , arguments = ["n"]
                , command = "c n"
                }
        command = Alias alias
     in do
            Result{output, continue} <- run command axioms [claim] claim
            let expectedOutput =
                    makeAuxReplOutput . showAliasError $ UnknownCommand
            output `equalsOutput` expectedOutput
            continue `equals` Continue

tryAlias :: IO ()
tryAlias =
    let axioms = []
        claim = emptyClaim
        name = "c"
        alias =
            AliasDefinition
                { name = "c"
                , arguments = ["n"]
                , command = "claim n"
                }
        stateT = \st -> st{aliases = Map.insert name alias (aliases st)}
        command = TryAlias $ ReplAlias "c" [SimpleArgument "0"]
     in do
            Result{output, continue} <-
                runWithState command axioms [claim] claim stateT
            output `equalsOutput` showRewriteRule claim
            continue `equals` Continue

unificationFailure :: IO ()
unificationFailure =
    let zero :: TermLike RewritingVariableName
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = mkAxiom one one
        axioms = [impossibleAxiom]
        claim = zeroToTen
        command = Try . ByIndex . Left $ AxiomIndex 0
     in do
            Result{logEntries, continue, state} <- run command axioms [claim] claim
            let expectedLogEntry =
                    mkDebugUnifyBottom "Distinct integer domain values" one zero
                actualdebugUnifyBottom =
                    catMaybes $ Log.fromEntry @DebugUnifyBottom <$> logEntries
            head actualdebugUnifyBottom `equals` expectedLogEntry
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 0

unificationFailureWithName :: IO ()
unificationFailureWithName =
    let zero :: TermLike RewritingVariableName
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = mkNamedAxiom one one "impossible"
        axioms = [impossibleAxiom]
        claim = zeroToTen
        command = Try . ByName . RuleName $ "impossible"
     in do
            Result{logEntries, continue, state} <- run command axioms [claim] claim
            let expectedLogEntry =
                    mkDebugUnifyBottom "Distinct integer domain values" one zero
                actualdebugUnifyBottom =
                    catMaybes $ Log.fromEntry @DebugUnifyBottom <$> logEntries
            head actualdebugUnifyBottom `equals` expectedLogEntry
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 0

unificationSuccess :: IO ()
unificationSuccess = do
    let zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = mkAxiom zero one
        axioms = [axiom]
        claim = zeroToTen
        command = Try . ByIndex . Left $ AxiomIndex 0
        expectedOutput = formatUnifiers (Condition.top :| [])

    Result{output, continue, state} <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 0

unificationSuccessWithName :: IO ()
unificationSuccessWithName = do
    let zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = mkNamedAxiom zero one "0to1"
        axioms = [axiom]
        claim = zeroToTen
        command = Try . ByName . RuleName $ "0to1"
        expectedOutput = formatUnifiers (Condition.top :| [])

    Result{output, continue, state} <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 0

forceFailure :: IO ()
forceFailure =
    let zero :: TermLike RewritingVariableName
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = mkAxiom one one
        axioms = [impossibleAxiom]
        claim = zeroToTen
        command = TryF . ByIndex . Left $ AxiomIndex 0
     in do
            Result{logEntries, continue, state} <- run command axioms [claim] claim
            let expectedLogEntry =
                    mkDebugUnifyBottom "Distinct integer domain values" one zero
                actualdebugUnifyBottom =
                    catMaybes $ Log.fromEntry @DebugUnifyBottom <$> logEntries
            head actualdebugUnifyBottom `equals` expectedLogEntry
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 0

forceFailureWithName :: IO ()
forceFailureWithName =
    let zero :: TermLike RewritingVariableName
        zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        impossibleAxiom = mkNamedAxiom one one "impossible"
        axioms = [impossibleAxiom]
        claim = zeroToTen
        command = TryF . ByName . RuleName $ "impossible"
     in do
            Result{logEntries, continue, state} <- run command axioms [claim] claim
            let expectedLogEntry =
                    mkDebugUnifyBottom "Distinct integer domain values" one zero
                actualdebugUnifyBottom =
                    catMaybes $ Log.fromEntry @DebugUnifyBottom <$> logEntries
            head actualdebugUnifyBottom `equals` expectedLogEntry
            continue `equals` Continue
            state `hasCurrentNode` ReplNode 0

forceSuccess :: IO ()
forceSuccess = do
    let zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = mkAxiom zero one
        axioms = [axiom]
        claim = zeroToTen
        command = TryF . ByIndex . Left $ AxiomIndex 0
        expectedOutput = mempty

    Result{output, continue, state} <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 1

tryResultsInProven :: IO ()
tryResultsInProven = do
    let zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = mkAxiom zero one
        axioms = [axiom]
        claim = zeroToZero
        command = TryF . ByIndex . Left $ AxiomIndex 0
        expectedOutput =
            makeAuxReplOutput
                "The proof was proven without applying any rewrite rules."

    Result{output, continue, state} <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 0

forceSuccessWithName :: IO ()
forceSuccessWithName = do
    let zero = Int.asInternal intSort 0
        one = Int.asInternal intSort 1
        axiom = mkNamedAxiom zero one "0to1"
        axioms = [axiom]
        claim = zeroToTen
        command = TryF . ByName . RuleName $ "0to1"
        expectedOutput = mempty

    Result{output, continue, state} <- run command axioms [claim] claim
    output `equalsOutput` expectedOutput
    continue `equals` Continue
    state `hasCurrentNode` ReplNode 1

proofStatus :: IO ()
proofStatus =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        command = ProofStatus
        expectedProofStatus =
            StrictMap.fromList
                [ (ClaimIndex 0, InProgress [0])
                , (ClaimIndex 1, NotStarted)
                ]
     in do
            Result{output, continue} <-
                run command axioms claims claim
            output `equalsOutput` makeAuxReplOutput (showProofStatus expectedProofStatus)
            continue `equals` Continue

showCurrentClaim :: IO ()
showCurrentClaim =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = []
        command = ShowClaim Nothing
        expectedCindex = ClaimIndex 0
     in do
            Result{output, continue} <-
                run command axioms claims claim
            equalsOutput
                output
                $ makeAuxReplOutput (showCurrentClaimIndex expectedCindex)
                    <> (makeKoreReplOutput . unparseToString $ zeroToTen)
            continue `equals` Continue

showClaim1 :: IO ()
showClaim1 =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = []
        command = ShowClaim (Just . Left . ClaimIndex $ 1)
        expectedClaim = emptyClaim
     in do
            Result{output, continue} <-
                run command axioms claims claim
            output `equalsOutput` showRewriteRule expectedClaim
            continue `equals` Continue

showClaimByName :: IO ()
showClaimByName =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = []
        command = ShowClaim (Just . Right . RuleName $ "0to10Claim")
        expectedClaim = zeroToTen
     in do
            Result{output, continue} <-
                run command axioms claims claim
            output `equalsOutput` showRewriteRule expectedClaim
            continue `equals` Continue

showAxiomByName :: IO ()
showAxiomByName =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        command = ShowAxiom (Right . RuleName $ "add1Axiom")
        expectedAxiom = add1
     in do
            Result{output, continue} <-
                run command axioms claims claim
            output `equalsOutput` showRewriteRule expectedAxiom
            continue `equals` Continue

logUpdatesState :: IO ()
logUpdatesState = do
    let axioms = []
        claim = emptyClaim
        options =
            GeneralLogOptions
                { logLevel = Log.Info
                , logEntries =
                    Map.keysSet . Log.typeToText $ Log.registry
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , timestampsSwitch = Log.TimestampsEnable
                }
        command = Log options
    Result{output, continue, state} <-
        run command axioms [claim] claim
    output `equalsOutput` mempty
    continue `equals` Continue
    state `hasLogging` generalLogOptionsTransformer options

debugAttemptEquationUpdatesState :: IO ()
debugAttemptEquationUpdatesState = do
    let axioms = []
        claim = emptyClaim
        options =
            Log.DebugAttemptEquationOptions $ HashSet.fromList ["symbol"]
        command = DebugAttemptEquation options
    Result{output, continue, state} <-
        run command axioms [claim] claim
    output `equalsOutput` mempty
    continue `equals` Continue
    hasLogging state (debugAttemptEquationTransformer options)

debugApplyEquationUpdatesState :: IO ()
debugApplyEquationUpdatesState = do
    let axioms = []
        claim = emptyClaim
        options =
            Log.DebugApplyEquationOptions $ HashSet.fromList ["symbol"]
        command = DebugApplyEquation options
    Result{output, continue, state} <-
        run command axioms [claim] claim
    output `equalsOutput` mempty
    continue `equals` Continue
    hasLogging state (debugApplyEquationTransformer options)

debugEquationUpdatesState :: IO ()
debugEquationUpdatesState = do
    let axioms = []
        claim = emptyClaim
        options =
            Log.DebugEquationOptions $ HashSet.fromList ["symbol"]
        command = DebugEquation options
    Result{output, continue, state} <-
        run command axioms [claim] claim
    output `equalsOutput` mempty
    continue `equals` Continue
    hasLogging state (debugEquationTransformer options)

proveSecondClaim :: IO ()
proveSecondClaim =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        indexOrName = Left . ClaimIndex $ 1
        command = Prove indexOrName
        expectedClaimIndex = ClaimIndex 1
     in do
            Result{output, continue, state} <-
                run command axioms claims claim
            output `equalsOutput` makeAuxReplOutput (showClaimSwitch indexOrName)
            state `hasCurrentClaimIndex` expectedClaimIndex
            continue `equals` Continue

proveSecondClaimByName :: IO ()
proveSecondClaimByName =
    let claims = [zeroToTen, emptyClaim]
        claim = zeroToTen
        axioms = [add1]
        indexOrName = Right . RuleName $ "emptyClaim"
        command = Prove indexOrName
        expectedClaimIndex = ClaimIndex 1
     in do
            Result{output, continue, state} <-
                run command axioms claims claim
            output `equalsOutput` makeAuxReplOutput (showClaimSwitch indexOrName)
            state `hasCurrentClaimIndex` expectedClaimIndex
            continue `equals` Continue

add1 :: Axiom
add1 =
    mkNamedAxiom n plusOne "add1Axiom"
  where
    one = Int.asInternal intSort 1
    n = mkElemVar $ ruleElementVariableFromId "x" intSort
    plusOne = n `addInt` one

zeroToTen :: SomeClaim
zeroToTen =
    OnePath . OnePathClaim $
        claimWithName zero ten "0to10Claim"
  where
    zero = Int.asInternal intSort 0
    ten = Int.asInternal intSort 10

emptyClaim :: SomeClaim
emptyClaim =
    OnePath . OnePathClaim $
        claimWithName
            (mkBottom kSort)
            (mkBottom kSort)
            "emptyClaim"

zeroToZero :: SomeClaim
zeroToZero =
    AllPath . AllPathClaim $
        claimWithName zero zero "0to0Claim"
  where
    zero = Int.asInternal intSort 0

mkNamedAxiom ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    String ->
    Axiom
mkNamedAxiom left right name =
    rulePattern left right
        & Lens.set (field @"attributes" . typed @Attribute.Label) label
        & RewriteRule
        & coerce
  where
    label = Attribute.Label . pure $ pack name

claimWithName ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    String ->
    ClaimPattern
claimWithName leftTerm rightTerm name =
    let left =
            Pattern.fromTermLike leftTerm
        right =
            Pattern.fromTermLike rightTerm
                & OrPattern.fromPattern
     in mkClaimPattern left right []
            & Lens.set (field @"attributes" . typed @Attribute.Label) label
  where
    label = Attribute.Label . pure $ pack name

mkAxiom ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Axiom
mkAxiom left right =
    rulePattern left right
        & RewriteRule
        & coerce

run ::
    ReplCommand ->
    [Axiom] ->
    [SomeClaim] ->
    SomeClaim ->
    IO Result
run command axioms claims claim =
    runWithState command axioms claims claim id

runWithState ::
    ReplCommand ->
    [Axiom] ->
    [SomeClaim] ->
    SomeClaim ->
    (ReplState -> ReplState) ->
    IO Result
runWithState command axioms claims claim stateTransformer = do
    startTime <- getTime Monotonic
    let logger = mempty
    output <- newIORef (mempty :: ReplOutput)
    mvar <- newMVar logger
    ma <- newEmptyMVar
    let state = stateTransformer $ mkState startTime axioms claims claim
    let config = mkConfig mvar claims ma
        runLogger =
            runTestLoggerT
                . liftSimplifier
                . flip runStateT state
                . flip runReaderT config
                . runInputT defaultSettings
    ((c, s), logEntries) <-
        runLogger $
            replInterpreter0
                (modifyAuxOutput output)
                (modifyKoreOutput output)
                command

    output' <- readIORef output
    return $ Result output' c s logEntries
  where
    liftSimplifier = SMT.runNoSMT . Kore.runSimplifier testEnv

    modifyAuxOutput :: IORef ReplOutput -> PrintAuxOutput
    modifyAuxOutput ref = PrintAuxOutput $ \s -> liftIO $ modifyIORef ref (appReplOut . AuxOut $ s)

    modifyKoreOutput :: IORef ReplOutput -> PrintKoreOutput
    modifyKoreOutput ref = PrintKoreOutput $ \s -> liftIO $ modifyIORef ref (appReplOut . KoreOut $ s)

data Result = Result
    { output :: ReplOutput
    , continue :: ReplStatus
    , state :: ReplState
    , logEntries :: [Log.SomeEntry]
    }

equals :: (Eq a, Show a) => a -> a -> Assertion
equals = (@?=)

equalsOutput :: ReplOutput -> ReplOutput -> Assertion
equalsOutput actual expected =
    actual @?= expected

hasCurrentNode :: ReplState -> ReplNode -> IO ()
hasCurrentNode st n = do
    node st `equals` n
    graphNode <- evalStateT (getTargetNode justNode) st
    graphNode `equals` justNode
  where
    justNode = Just n

hasAlias :: ReplState -> AliasDefinition -> IO ()
hasAlias st alias@AliasDefinition{name} =
    let aliasMap = aliases st
        actual = name `Map.lookup` aliasMap
     in actual `equals` Just alias

hasLogging ::
    ReplState ->
    (Log.KoreLogOptions -> Log.KoreLogOptions) ->
    IO ()
hasLogging st transformer =
    let actualLogging = koreLogOptions st
     in actualLogging `equals` transformer actualLogging

hasCurrentClaimIndex :: ReplState -> ClaimIndex -> IO ()
hasCurrentClaimIndex st expectedClaimIndex =
    let actualClaimIndex = claimIndex st
     in actualClaimIndex `equals` expectedClaimIndex

mkState ::
    TimeSpec ->
    [Axiom] ->
    [SomeClaim] ->
    SomeClaim ->
    ReplState
mkState startTime axioms claims claim =
    ReplState
        { axioms = axioms
        , claims = claims
        , claim = claim
        , claimIndex = ClaimIndex 0
        , graphs = Map.singleton (ClaimIndex 0) graph'
        , node = ReplNode 0
        , commands = Seq.empty
        , omit = mempty
        , labels = Map.singleton (ClaimIndex 0) Map.empty
        , aliases = Map.empty
        , koreLogOptions =
            Log.defaultKoreLogOptions (Log.ExeName "kore-repl") startTime
        , stepTimeout = Nothing
        , stepTime = DisableStepTime
        , enableMovingAverage = DisableMovingAverage
        }
  where
    graph' = emptyExecutionGraph claim

mkConfig ::
    MVar (Log.LogAction IO Log.SomeEntry) ->
    [SomeClaim] ->
    MVar (StepMovingAverage) ->
    Config
mkConfig logger claims' ma =
    Config
        { stepper = stepper0
        , unifier = unificationProcedure
        , logger
        , outputFile = OutputFile Nothing
        , mainModuleName = ModuleName "TEST"
        , kFileLocations = KFileLocations []
        , kompiledDir = KompiledDir ""
        , korePrintCommand = KorePrintCommand "kore-print"
        }
  where
    stepper0 ::
        Maybe StepTimeout ->
        EnableMovingAverage ->
        [Axiom] ->
        ExecutionGraph ->
        ReplNode ->
        Simplifier (Maybe ExecutionGraph)
    stepper0 _ enableMA axioms' graph (ReplNode node) =
        proveClaimStep
            Nothing
            Nothing
            ma
            enableMA
            EnabledStuckCheck
            DisallowedVacuous
            claims'
            axioms'
            graph
            node

formatUnifiers ::
    NonEmpty (Condition RewritingVariableName) ->
    ReplOutput
formatUnifiers = formatUnificationMessage . Just
