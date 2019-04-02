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

import           Control.Exception
                 ( AsyncException (UserInterrupt) )
import           Control.Lens
                 ( (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad.Catch
                 ( MonadCatch, catch )
import           Control.Monad.Extra
                 ( whileM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( MonadState, StateT )
import           Control.Monad.State.Strict
                 ( evalStateT, get )
import           Control.Monad.State.Strict
                 ( lift )
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( listToMaybe )
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( parseMaybe )

import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.OnePath.Verification
                 ( verifyClaimStep )
import           Kore.OnePath.Verification
                 ( Axiom )
import           Kore.OnePath.Verification
                 ( Claim )
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Repl.Parser
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import           Kore.Step.Simplification.Data
                 ( StepPatternSimplifier )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier )
import qualified Kore.Step.Strategy as Strategy

-- | Runs the repl for proof mode. It requires all the tooling and simplifiers
-- that would otherwise be required in the proof and allows for step-by-step
-- execution of proofs. Currently works via stdin/stdout interaction.
runRepl
    :: forall level
    .  MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^ tools required for the proof
    -> StepPatternSimplifier level
    -- ^ pattern simplifier
    -> PredicateSubstitutionSimplifier level
    -- ^ predicate simplifier
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ builtin simplifier
    -> [Axiom level]
    -- ^ list of axioms to used in the proof
    -> [Claim level]
    -- ^ list of claims to be proven
    -> Simplifier ()
runRepl tools simplifier predicateSimplifier axiomToIdSimplifier axioms' claims'
  = do
    replGreeting
    evalStateT (whileM repl0) state

  where
    repl0 :: StateT (ReplState level) Simplifier Bool
    repl0 = do
        command <- maybe ShowUsage id . parseMaybe commandParser <$> prompt
        replInterpreter command

    state :: ReplState level
    state =
        ReplState
            { axioms  = axioms'
            , claims  = claims'
            , claim   = firstClaim
            , graph   = firstClaimExecutionGraph
            , node    = (Strategy.root firstClaimExecutionGraph)
            -- TODO(Vladimir): should initialize this to the value obtained from
            -- the frontend via '--omit-labels'.
            , omit    = []
            , stepper = stepper0
            , labels  = Map.empty
            }

    firstClaim :: Claim level
    firstClaim = maybe (error "No claims found") id $ listToMaybe claims'

    firstClaimExecutionGraph :: ExecutionGraph level
    firstClaimExecutionGraph = emptyExecutionGraph firstClaim

    stepper0 :: StateT (ReplState level) Simplifier Bool
    stepper0 = do
        ReplState { claims , axioms , graph , claim , node } <- get
        if Graph.outdeg (Strategy.graph graph) node == 0
            then do
                graph' <-
                    lift
                        . catchInterruptWithDefault graph
                        $ verifyClaimStep
                            tools
                            simplifier
                            predicateSimplifier
                            axiomToIdSimplifier
                            claim
                            claims
                            axioms
                            graph
                            node
                lensGraph .= graph'
                pure True
            else pure False

    catchInterruptWithDefault :: MonadCatch m => MonadIO m => a -> m a -> m a
    catchInterruptWithDefault def sa =
        catch sa $ \UserInterrupt -> do
            liftIO $ putStrLn "Step evaluation interrupted."
            pure def

    replGreeting :: MonadIO m => m ()
    replGreeting =
        liftIO $
            putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

    prompt :: MonadIO m => MonadState (ReplState level) m => m String
    prompt = do
        node <- Lens.use lensNode
        liftIO $ do
            putStr $ "Kore (" <> show node <> ")> "
            hFlush stdout
            getLine
