{- |
Module      : Kore.Repl
Description : Proof REPL
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
module Kore.Repl (
    runRepl,
) where

import Control.Concurrent.MVar
import qualified Control.Lens as Lens
import Control.Monad (
    forever,
 )
import Control.Monad.Catch (
    MonadMask,
 )
import qualified Control.Monad.Catch as Exception
import Control.Monad.RWS.Strict (
    RWST,
    execRWST,
 )
import Control.Monad.Reader (
    ReaderT (..),
 )
import Control.Monad.State.Strict (
    MonadState,
    StateT,
    evalStateT,
 )
import Data.Generics.Product
import Data.Generics.Wrapped
import qualified Data.Graph.Inductive.Graph as Graph
import Data.List (
    findIndex,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import Kore.Attribute.Definition
import Kore.Attribute.RuleIndex (
    RuleIndex (..),
 )
import qualified Kore.Attribute.RuleIndex as Attribute
import Kore.Internal.TermLike (
    TermLike,
    mkSortVariable,
    mkTop,
 )
import qualified Kore.Log as Log
import Kore.Log.ErrorException (
    errorException,
 )
import Kore.Reachability (
    SomeClaim,
    lensClaimPattern,
 )
import Kore.Reachability.Claim
import qualified Kore.Reachability.Claim as Claim
import Kore.Reachability.Prove
import Kore.Repl.Data
import Kore.Repl.Interpreter
import Kore.Repl.Parser
import Kore.Repl.State
import Kore.Step.Simplification.Data (
    MonadSimplify,
 )
import qualified Kore.Step.Strategy as Strategy
import Kore.Syntax.Module (
    ModuleName (..),
 )
import Kore.Syntax.Variable
import Kore.Unification.Procedure (
    unificationProcedure,
 )
import Kore.Unparser (
    unparseToString,
 )
import Prelude.Kore
import Prof (
    MonadProf,
 )
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    getTime,
 )
import System.IO (
    hFlush,
    hPutStrLn,
    stderr,
    stdout,
 )
import Text.Megaparsec (
    parseMaybe,
 )

{- | Runs the repl for proof mode. It requires all the tooling and simplifiers
 that would otherwise be required in the proof and allows for step-by-step
 execution of proofs. Currently works via stdin/stdout interaction.
-}
runRepl ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    MonadProf m =>
    MonadMask m =>
    -- | list of axioms to used in the proof
    [Axiom] ->
    -- | list of claims to be proven
    [SomeClaim] ->
    MVar (Log.LogAction IO Log.ActualEntry) ->
    -- | optional script
    ReplScript ->
    -- | mode to run in
    ReplMode ->
    -- | optional flag for output in run mode
    ScriptModeOutput ->
    -- | optional output file
    OutputFile ->
    ModuleName ->
    Log.KoreLogOptions ->
    KFileLocations ->
    m ()
runRepl _ [] _ _ _ _ outputFile _ _ _ =
    let printTerm = maybe putStrLn writeFile (unOutputFile outputFile)
     in liftIO . printTerm . unparseToString $ topTerm
  where
    topTerm :: TermLike VariableName
    topTerm = mkTop $ mkSortVariable "R"
runRepl
    axioms'
    claims'
    logger
    replScript
    replMode
    scriptModeOutput
    outputFile
    mainModuleName
    logOptions
    kFileLocations =
        do
            startTime <- liftIO $ getTime Monotonic
            (newState, _) <-
                (\rwst -> execRWST rwst config (state startTime)) $
                    evaluateScript replScript scriptModeOutput
            case replMode of
                Interactive -> do
                    replGreeting
                    flip evalStateT newState $
                        flip runReaderT config $
                            forever repl0
                RunScript ->
                    runReplCommand Exit newState
      where
        runReplCommand :: ReplCommand -> ReplState -> m ()
        runReplCommand cmd st =
            void $
                flip evalStateT st $
                    flip runReaderT config $
                        replInterpreter printIfNotEmpty cmd

        evaluateScript ::
            ReplScript ->
            ScriptModeOutput ->
            RWST (Config m) String ReplState m ()
        evaluateScript script outputFlag =
            maybe
                (pure ())
                (flip parseEvalScript outputFlag)
                (unReplScript script)

        repl0 :: ReaderT (Config m) (StateT ReplState m) ()
        repl0 = do
            str <- prompt
            let command =
                    fromMaybe ShowUsage $ parseMaybe commandParser (Text.pack str)
                silent = pure ()
            when (shouldStore command) $ field @"commands" Lens.%= (Seq.|> str)
            saveSessionWithMessage silent ".sessionCommands"
            void $ replInterpreter printIfNotEmpty command

        state :: TimeSpec -> ReplState
        state startTime =
            ReplState
                { axioms = addIndexesToAxioms axioms'
                , claims = addIndexesToClaims claims'
                , claim = firstClaim
                , claimIndex = firstClaimIndex
                , graphs = Map.singleton firstClaimIndex firstClaimExecutionGraph
                , node = ReplNode (Strategy.root firstClaimExecutionGraph)
                , commands = Seq.empty
                , -- TODO(Vladimir): should initialize this to the value obtained from
                  -- the frontend via '--omit-labels'.
                  omit = mempty
                , labels = Map.empty
                , aliases = Map.empty
                , koreLogOptions =
                    logOptions
                        { Log.exeName = Log.ExeName "kore-repl"
                        , Log.startTime = startTime
                        }
                }

        config :: Config m
        config =
            Config
                { stepper = stepper0
                , unifier = unificationProcedure
                , logger
                , outputFile
                , mainModuleName
                , kFileLocations
                }

        firstClaimIndex :: ClaimIndex
        firstClaimIndex =
            ClaimIndex
                . fromMaybe (error "No claims found")
                $ findIndex (not . isTrusted) claims'

        addIndexesToAxioms ::
            [Axiom] ->
            [Axiom]
        addIndexesToAxioms =
            initializeRuleIndexes Attribute.AxiomIndex lensAttribute
          where
            lensAttribute = _Unwrapped . _Unwrapped . field @"attributes"

        addIndexesToClaims ::
            [SomeClaim] ->
            [SomeClaim]
        addIndexesToClaims =
            initializeRuleIndexes Attribute.ClaimIndex lensAttribute
          where
            lensAttribute = lensClaimPattern . field @"attributes"

        initializeRuleIndexes ctor lens rules =
            zipWith addIndex rules [0 ..]
          where
            addIndex rule index =
                Lens.set
                    (lens . field @"identifier")
                    (index & ctor & Just & RuleIndex)
                    rule

        firstClaim :: SomeClaim
        firstClaim = claims' !! unClaimIndex firstClaimIndex

        firstClaimExecutionGraph :: ExecutionGraph
        firstClaimExecutionGraph = emptyExecutionGraph firstClaim

        stepper0 ::
            [SomeClaim] ->
            [Axiom] ->
            ExecutionGraph ->
            ReplNode ->
            m ExecutionGraph
        stepper0 claims axioms graph rnode = do
            let node = unReplNode rnode
            if Graph.outdeg (Strategy.graph graph) node == 0
                then
                    proveClaimStep claims axioms graph node
                        & Exception.handle (withConfigurationHandler graph)
                        & Exception.handle (someExceptionHandler graph)
                else pure graph

        withConfigurationHandler :: a -> Claim.WithConfiguration -> m a
        withConfigurationHandler
            _
            (Claim.WithConfiguration lastConfiguration someException) =
                do
                    liftIO $
                        hPutStrLn
                            stderr
                            ("// Last configuration:\n" <> unparseToString lastConfiguration)
                    Exception.throwM someException

        someExceptionHandler :: a -> Exception.SomeException -> m a
        someExceptionHandler a someException = do
            case Exception.fromException someException of
                Just (Log.SomeEntry entry) ->
                    Log.logEntry entry
                Nothing ->
                    errorException someException
            pure a

        replGreeting :: m ()
        replGreeting =
            liftIO $
                putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

        prompt :: MonadIO n => MonadState ReplState n => n String
        prompt = do
            node <- Lens.use (field @"node")
            liftIO $ do
                putStr $ "Kore (" <> show (unReplNode node) <> ")> "
                hFlush stdout
                getLine
