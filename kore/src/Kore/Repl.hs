{-|
Module      : Kore.Repl
Description : Proof REPL
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl
    ( runRepl
    ) where

import Control.Concurrent.MVar
import Control.Exception
    ( AsyncException (UserInterrupt)
    )
import qualified Control.Lens as Lens hiding
    ( makeLenses
    )
import Control.Monad
    ( forever
    , void
    , when
    )
import Control.Monad.Catch
    ( MonadCatch
    , catch
    , catchAll
    )
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
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
import Data.Coerce
    ( coerce
    )
import Data.Generics.Product
import qualified Data.Graph.Inductive.Graph as Graph
import Data.List
    ( findIndex
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Sequence as Seq
import Kore.Attribute.RuleIndex
import System.IO
    ( hFlush
    , stdout
    )
import Text.Megaparsec
    ( parseMaybe
    )

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Logger as Logger
import Kore.Repl.Data
import Kore.Repl.Interpreter
import Kore.Repl.Parser
import Kore.Repl.State
import qualified Kore.Step.Rule as Rule
import Kore.Step.Simplification.Data
    ( MonadSimplify
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Strategies.Goal
import Kore.Strategies.Verification
import Kore.Syntax.Variable
import Kore.Unification.Procedure
    ( unificationProcedure
    )

-- | Runs the repl for proof mode. It requires all the tooling and simplifiers
-- that would otherwise be required in the proof and allows for step-by-step
-- execution of proofs. Currently works via stdin/stdout interaction.
runRepl
    :: forall claim axiom m
    .  MonadSimplify m
    => MonadIO m
    => MonadCatch m
    => Claim claim
    => axiom ~ Rule claim
    => [axiom]
    -- ^ list of axioms to used in the proof
    -> [claim]
    -- ^ list of claims to be proven
    -> MVar (Logger.LogAction IO Logger.SomeEntry)
    -> ReplScript
    -- ^ optional script
    -> ReplMode
    -- ^ mode to run in
    -> OutputFile
    -- ^ optional output file
    -> m ()
runRepl axioms' claims' logger replScript replMode outputFile = do
    (newState, _) <-
            (\rwst -> execRWST rwst config state)
            $ evaluateScript replScript
    case replMode of
        Interactive -> do
            replGreeting
            flip evalStateT newState
                $ flip runReaderT config
                $ forever repl0
        RunScript ->
            runReplCommand Exit newState

  where

    runReplCommand :: ReplCommand -> ReplState claim -> m ()
    runReplCommand cmd st =
        void
            $ flip evalStateT st
            $ flip runReaderT config
            $ replInterpreter printIfNotEmpty cmd

    evaluateScript :: ReplScript -> RWST (Config claim m) String (ReplState claim) m ()
    evaluateScript = maybe (pure ()) parseEvalScript . unReplScript

    repl0 :: ReaderT (Config claim m) (StateT (ReplState claim) m) ()
    repl0 = do
        str <- prompt
        let command = fromMaybe ShowUsage $ parseMaybe commandParser str
        when (shouldStore command) $ field @"commands" Lens.%= (Seq.|> str)
        void $ replInterpreter printIfNotEmpty command

    state :: ReplState claim
    state =
        ReplState
            { axioms     = addIndexesToAxioms axioms'
            , claims     = addIndexesToClaims (length axioms') claims'
            , claim      = firstClaim
            , claimIndex = firstClaimIndex
            , graphs     = Map.singleton firstClaimIndex firstClaimExecutionGraph
            , node       = ReplNode (Strategy.root firstClaimExecutionGraph)
            , commands   = Seq.empty
            -- TODO(Vladimir): should initialize this to the value obtained from
            -- the frontend via '--omit-labels'.
            , omit       = mempty
            , labels     = Map.empty
            , aliases    = Map.empty
            , logging    = (Logger.Debug, mempty, NoLogging)
            }

    config :: Config claim m
    config =
        Config
            { stepper    = stepper0
            , unifier    = unificationProcedure
            , logger
            , outputFile
            }

    firstClaimIndex :: ClaimIndex
    firstClaimIndex =
        ClaimIndex
        . fromMaybe (error "No claims found")
        $ findIndex (not . isTrusted) claims'

    addIndexesToAxioms
        :: [axiom]
        -> [axiom]
    addIndexesToAxioms axs =
        fmap addIndex (zip axs [0..])

    addIndexesToClaims
        :: Int
        -> [claim]
        -> [claim]
    addIndexesToClaims len cls =
        fmap
            (coerce . addIndex)
            (zip (fmap coerce cls) [len..])

    addIndex
        :: (axiom, Int)
        -> axiom
    addIndex (rw, n) =
        modifyAttribute (mapAttribute n (getAttribute rw)) rw

    modifyAttribute
        :: Attribute.Axiom
        -> axiom
        -> axiom
    modifyAttribute att rule =
        let rp = axiomToRulePatt rule in
            coerce $ rp { Rule.attributes = att }

    axiomToRulePatt :: axiom -> Rule.RulePattern Variable
    axiomToRulePatt = coerce

    getAttribute :: axiom -> Attribute.Axiom
    getAttribute = Rule.attributes . axiomToRulePatt

    mapAttribute :: Int -> Attribute.Axiom -> Attribute.Axiom
    mapAttribute n attr =
        Lens.over (field @"identifier") (makeRuleIndex n) attr

    makeRuleIndex :: Int -> RuleIndex -> RuleIndex
    makeRuleIndex n _ = RuleIndex (Just n)

    firstClaim :: Claim claim => claim
    firstClaim =
        claims' !! unClaimIndex firstClaimIndex

    firstClaimExecutionGraph :: ExecutionGraph axiom
    firstClaimExecutionGraph = emptyExecutionGraph firstClaim

    stepper0
        :: claim
        -> [claim]
        -> [axiom]
        -> ExecutionGraph axiom
        -> ReplNode
        -> m (ExecutionGraph axiom)
    stepper0 claim claims axioms graph rnode = do
        let node = unReplNode rnode
        if Graph.outdeg (Strategy.graph graph) node == 0
            then
                catchEverything graph
                $ catchInterruptWithDefault graph
                $ verifyClaimStep claim claims axioms graph node
            else pure graph

    catchInterruptWithDefault :: MonadCatch m => MonadIO m => a -> m a -> m a
    catchInterruptWithDefault def sa =
        catch sa $ \UserInterrupt -> do
            liftIO $ putStrLn "Step evaluation interrupted."
            pure def

    catchEverything :: MonadCatch m => MonadIO m => a -> m a -> m a
    catchEverything def sa =
        catchAll sa $ \e -> do
            liftIO $ putStrLn "Stepper evaluation errored."
            liftIO $ putStrLn (show e)
            pure def

    replGreeting :: MonadIO m => m ()
    replGreeting =
        liftIO $
            putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

    prompt :: MonadIO n => MonadState (ReplState claim) n => n String
    prompt = do
        node <- Lens.use (field @"node")
        liftIO $ do
            putStr $ "Kore (" <> show (unReplNode node) <> ")> "
            hFlush stdout
            getLine
