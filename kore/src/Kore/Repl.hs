{-|
Module      : Kore.Repl
Description : Proof REPL
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
{-# LANGUAGE Strict #-}

module Kore.Repl
    ( runRepl
    ) where

import Prelude.Kore

import Control.Concurrent.MVar
import Control.Exception
    ( AsyncException (UserInterrupt)
    , fromException
    )
import qualified Control.Lens as Lens
import Control.Monad
    ( forever
    , void
    )
import Control.Monad.Catch
    ( MonadMask
    )
import qualified Control.Monad.Catch as Exception
import Control.Monad.Reader
    ( ReaderT (..)
    )
import Control.Monad.RWS.Strict
    ( RWST
    , execRWST
    )
import Control.Monad.State.Strict
    ( MonadState
    , StateT
    , evalStateT
    )
import Data.Generics.Product
import Data.Generics.Wrapped
import qualified Data.Graph.Inductive.Graph as Graph
import Data.List
    ( findIndex
    )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import Kore.Attribute.RuleIndex
    ( RuleIndex (..)
    )
import qualified Kore.Attribute.RuleIndex as Attribute
import System.IO
    ( hFlush
    , stdout
    )
import Text.Megaparsec
    ( parseMaybe
    )

import Kore.Internal.TermLike
    ( TermLike
    , mkSortVariable
    , mkTop
    )
import qualified Kore.Log as Log
import Kore.Reachability
    ( SomeClaim
    , lensClaimPattern
    )
import Kore.Reachability.Claim
import Kore.Reachability.Prove
import Kore.Repl.Data
import Kore.Repl.Interpreter
import Kore.Repl.Parser
import Kore.Repl.State
import Kore.Step.Simplification.Data
    ( MonadSimplify
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Syntax.Module
    ( ModuleName (..)
    )
import Kore.Syntax.Variable
import Prof
    ( MonadProf
    )

import Kore.Log.ErrorException
    ( errorException
    )
import Kore.Unification.Procedure
    ( unificationProcedure
    )
import Kore.Unparser
    ( unparseToString
    )
import System.Clock
    ( Clock (Monotonic)
    , TimeSpec
    , getTime
    )

-- | Runs the repl for proof mode. It requires all the tooling and simplifiers
-- that would otherwise be required in the proof and allows for step-by-step
-- execution of proofs. Currently works via stdin/stdout interaction.
runRepl
    :: forall m
    .  MonadSimplify m
    => MonadIO m
    => MonadProf m
    => MonadMask m
    => [Axiom]
    -- ^ list of axioms to used in the proof
    -> [SomeClaim]
    -- ^ list of claims to be proven
    -> MVar (Log.LogAction IO Log.ActualEntry)
    -> ReplScript
    -- ^ optional script
    -> ReplMode
    -- ^ mode to run in
    -> ScriptModeOutput
    -- ^ optional flag for output in run mode
    -> OutputFile
    -- ^ optional output file
    -> ModuleName
    -> Log.KoreLogOptions
    -> m ()
runRepl _ [] _ _ _ _ outputFile _ _ =
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
    = do
    startTime <- liftIO $ getTime Monotonic
    (newState, _) <-
            (\rwst -> execRWST rwst config (state startTime))
            $ evaluateScript replScript scriptModeOutput
    case replMode of
        Interactive -> do
            replGreeting
            flip evalStateT newState
                $ flip runReaderT config
                $ forever repl0
        RunScript ->
            runReplCommand Exit newState

  where

    runReplCommand :: ReplCommand -> ReplState -> m ()
    runReplCommand cmd st =
        void
            $ flip evalStateT st
            $ flip runReaderT config
            $ replInterpreter printIfNotEmpty cmd

    evaluateScript
        :: ReplScript
        -> ScriptModeOutput
        -> RWST (Config m) String ReplState m ()
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
        when (shouldStore command) $ field @"commands" Lens.%= (Seq.|> str)
        void $ replInterpreter printIfNotEmpty command

    state :: TimeSpec -> ReplState
    state startTime =
        ReplState
            { axioms         = addIndexesToAxioms axioms'
            , claims         = addIndexesToClaims claims'
            , claim          = firstClaim
            , claimIndex     = firstClaimIndex
            , graphs         = Map.singleton firstClaimIndex firstClaimExecutionGraph
            , node           = ReplNode (Strategy.root firstClaimExecutionGraph)
            , commands       = Seq.empty
            -- TODO(Vladimir): should initialize this to the value obtained from
            -- the frontend via '--omit-labels'.
            , omit           = mempty
            , labels         = Map.empty
            , aliases        = Map.empty
            , koreLogOptions =
                logOptions
                    { Log.exeName = Log.ExeName "kore-repl"
                    , Log.startTime = startTime
                    }
            }

    config :: Config m
    config =
        Config
            { stepper    = stepper0
            , unifier    = unificationProcedure
            , logger
            , outputFile
            , mainModuleName
            }

    firstClaimIndex :: ClaimIndex
    firstClaimIndex =
        ClaimIndex
        . fromMaybe (error "No claims found")
        $ findIndex (not . isTrusted) claims'

    addIndexesToAxioms
        :: [Axiom]
        -> [Axiom]
    addIndexesToAxioms =
        initializeRuleIndexes Attribute.AxiomIndex lensAttribute
      where
        lensAttribute = _Unwrapped . _Unwrapped . field @"attributes"

    addIndexesToClaims
        :: [SomeClaim]
        -> [SomeClaim]
    addIndexesToClaims =
        initializeRuleIndexes Attribute.ClaimIndex lensAttribute
      where
        lensAttribute = lensClaimPattern . field @"attributes"

    initializeRuleIndexes ctor lens rules =
        zipWith addIndex rules [0..]
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

    stepper0
        :: [SomeClaim]
        -> [Axiom]
        -> ExecutionGraph
        -> ReplNode
        -> m ExecutionGraph
    stepper0 claims axioms graph rnode = do
        let node = unReplNode rnode
        if Graph.outdeg (Strategy.graph graph) node == 0
            then
                proveClaimStep claims axioms graph node
                & catchInterruptWithDefault graph
                & catchEverything graph
            else pure graph

    catchInterruptWithDefault :: a -> m a -> m a
    catchInterruptWithDefault a =
        Exception.handle $ \case
            UserInterrupt -> do
                liftIO $ putStrLn "Step evaluation interrupted."
                pure a
            e -> Exception.throwM e

    catchEverything :: a -> m a -> m a
    catchEverything a =
        Exception.handleAll $ \e -> do
            case fromException e of
                Just (Log.SomeEntry entry) -> Log.logEntry entry
                Nothing -> errorException e
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
