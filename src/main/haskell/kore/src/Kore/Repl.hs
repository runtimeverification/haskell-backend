{-|
Module      : Kore.Repl
Description : Logging functions.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds    #-}
-- Added because stepper is only used via 'lensStepper' which is not detected

module Kore.Repl
    ( runRepl
    ) where

import           Control.Lens
                 ( (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import qualified Control.Lens.TH.Rules as Lens
import           Control.Monad.Extra
                 ( whileM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( StateT )
import           Control.Monad.State.Strict
                 ( evalStateT, get )
import           Control.Monad.State.Strict
                 ( lift )
import           Data.Functor
                 ( ($>) )
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.GraphViz as Graph
import           Data.Maybe
                 ( listToMaybe )
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( Parsec, parseMaybe, (<|>) )
import           Text.Megaparsec.Char
import           Text.Megaparsec.Char.Lexer
                 ( decimal, signed )

import qualified Kore.AST.Common as Kore
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.OnePath.Step
                 ( StrategyPattern (..) )
import           Kore.OnePath.Verification
                 ( verifyClaimStep )
import           Kore.OnePath.Verification
                 ( Axiom (..) )
import           Kore.OnePath.Verification
                 ( Claim (..) )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (..) )
import           Kore.Step.AxiomPatterns
                 ( RulePattern (..) )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import           Kore.Step.Simplification.Data
                 ( StepPatternSimplifier )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Unparser
                 ( unparseToString )

-- Type synonym for the actual type of the execution graph.
type ExecutionGraph level
    = Strategy.ExecutionGraph
        (StrategyPattern (CommonExpandedPattern level))

-- | State for the rep.
data ReplState level = ReplState
    { axioms    :: [Axiom level]
    -- ^ List of available axioms
    , claims    :: [Claim level]
    -- ^ List of claims to be proven
    , claim     :: Claim level
    -- ^ Currently focused claim in the repl
    , graph     :: ExecutionGraph level
    -- ^ Execution graph for the current proof; initialized with root = claim
    , node      :: Graph.Node
    -- ^ Currently selected node in the graph; initialized with node = root
    , stepper   :: StateT (ReplState level) Simplifier Bool
    -- ^ Stepper function, it is a partially applied 'verifyClaimStep'
    }

Lens.makeLenses ''ReplState

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
            axioms'
            claims'
            firstClaim
            firstClaimExecutionGraph
            (Strategy.root firstClaimExecutionGraph)
            stepper

    firstClaim :: Claim level
    firstClaim = maybe (error "No claims found") id . listToMaybe $ claims'


    firstClaimExecutionGraph :: ExecutionGraph level
    firstClaimExecutionGraph = emptyExecutionGraph firstClaim

    stepper :: StateT (ReplState level) Simplifier Bool
    stepper = do
        ReplState
            { claims
            , axioms
            , graph
            , claim
            , node
            } <- get
        if Graph.outdeg (Strategy.graph graph) node == 0
            then do
                graph' <- lift
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

    replGreeting :: MonadIO m => m ()
    replGreeting =
        liftIO $ putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

    prompt :: MonadIO m => m String
    prompt = liftIO $ do
        putStr "Kore> "
        hFlush stdout
        getLine

-- | List of available commands for the Repl. Note that we are always in a proof
-- state. We pick the first available Claim when we initialize the state.
data ReplCommand
    = ShowUsage
    -- ^ This is the default action in case parsing all others fail.
    | Help
    -- ^ Shows the help message.
    | ShowClaim !Int
    -- ^ Show the nth claim.
    | ShowAxiom !Int
    -- ^ Show the nth axiom.
    | Prove !Int
    -- ^ Drop the current proof state and re-initialize for the nth claim.
    | ShowGraph
    -- ^ Show the current execution graph.
    | ProveStep
    -- ^ Do one step proof from curent node, select the next state if unique.
    | SelectNode !Int
    -- ^ Select a different node in the graph.
    | ShowConfig
    -- ^ Show the configuration from the current node.
    | Exit
    -- ^ Exit the repl.

-- | Please remember to update this text whenever you update the ADT above.
helpText :: String
helpText =
    "Available commands in the Kore REPL: \n\
    \help                    shows this help message\n\
    \claim <n>               shows the nth claim\n\
    \axiom <n>               shows the nth axiom\n\
    \prove <n>               initializez proof mode for the nth claim\n\
    \graph                   shows the current proof graph\n\
    \step                    attempts to run a proof step at the current node \n\
    \select <n>              select node id 'n' from the graph\n\
    \config                  shows the config for the selected node\n\
    \exit                    exits the repl"

type Parser = Parsec String String

commandParser :: Parser ReplCommand
commandParser =
    help0
    <|> showClaim0
    <|> showAxiom0
    <|> prove0
    <|> showGraph0
    <|> proveStep0
    <|> selectNode0
    <|> showConfig0
    <|> exit0
    <|> pure ShowUsage
  where
    help0 :: Parser ReplCommand
    help0 = string "help" $> Help

    showClaim0 :: Parser ReplCommand
    showClaim0 = fmap ShowClaim $ string "claim" *> space *> decimal

    showAxiom0 :: Parser ReplCommand
    showAxiom0 = fmap ShowAxiom $ string "axiom" *> space *> decimal

    prove0 :: Parser ReplCommand
    prove0 = fmap Prove $ string "prove" *> space *> decimal

    showGraph0 :: Parser ReplCommand
    showGraph0 = ShowGraph <$ string "graph"

    proveStep0 :: Parser ReplCommand
    proveStep0 = ProveStep <$ string "step"

    selectNode0 :: Parser ReplCommand
    selectNode0 =
        fmap SelectNode $ string "select" *> space *> signed space decimal

    showConfig0 :: Parser ReplCommand
    showConfig0 = ShowConfig <$ string "show config"

    exit0 :: Parser ReplCommand
    exit0 = Exit <$ string "exit"

replInterpreter
    :: forall level
    .  MetaOrObject level
    => ReplCommand
    -> StateT (ReplState level) Simplifier Bool
replInterpreter =
    \case
        ShowUsage -> showUsage0 $> True
        Help -> help0 $> True
        ShowClaim c -> showClaim0 c $> True
        ShowAxiom a -> showAxiom0 a $> True
        Prove i -> prove0 i $> True
        ShowGraph -> showGraph0 $> True
        ProveStep -> proveStep0 $> True
        SelectNode i -> selectNode0 i $> True
        ShowConfig -> showConfig0 $> True
        Exit -> pure False
  where
    showUsage0 :: StateT st Simplifier ()
    showUsage0 =
        putStrLn' "Could not parse command, try using 'help'."

    help0 :: StateT st Simplifier ()
    help0 =
        putStrLn' helpText

    showClaim0 :: Int -> StateT (ReplState level) Simplifier ()
    showClaim0 index = do
        claim <- Lens.preuse $ lensClaims . Lens.element index
        putStrLn' $ maybe indexNotFound (unparseToString . unClaim) claim

    showAxiom0 :: Int -> StateT (ReplState level) Simplifier ()
    showAxiom0 index = do
        axiom <- Lens.preuse $ lensAxioms . Lens.element index
        putStrLn' $ maybe indexNotFound (unparseToString . unAxiom) axiom

    prove0 :: Int -> StateT (ReplState level) Simplifier ()
    prove0 index = do
        claim' <- Lens.preuse $ lensClaims . Lens.element index
        case claim' of
            Nothing -> putStrLn' indexNotFound
            Just claim -> do
                let
                    graph@Strategy.ExecutionGraph { root }
                        = emptyExecutionGraph claim
                lensGraph .= graph
                lensClaim .= claim
                lensNode  .= root
                putStrLn' "Execution Graph initiated"

    showGraph0 :: StateT (ReplState level) Simplifier ()
    showGraph0 = do
        Strategy.ExecutionGraph { graph } <- Lens.use lensGraph

        liftIO
            . (flip Graph.runGraphvizCanvas') Graph.Xlib
            . Graph.graphToDot Graph.nonClusteredParams
            $ graph

    proveStep0 :: StateT (ReplState level) Simplifier ()
    proveStep0 = do
        f <- Lens.use lensStepper
        res <- f
        if res
            then do
                Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
                node <- Lens.use lensNode
                let
                    context = Graph.context graph node
                case Graph.suc' context of
                    [] -> putStrLn' "No child nodes were found."
                    neighbors@(first' : _) -> do
                        lensNode .= first'
                        putStrLn'
                            $ "Found "
                            <> show (length neighbors)
                            <> " sub-state(s). Selecting state #"
                            <> show first'
            else putStrLn' "Node already evaluated."

    selectNode0 :: Int -> StateT (ReplState level) Simplifier ()
    selectNode0 i = do
        Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
        if i `elem` Graph.nodes graph
            then lensNode .= i
            else putStrLn' "Invalid node!"

    showConfig0 :: StateT (ReplState level) Simplifier ()
    showConfig0 = do
        ReplState { graph, node } <- get
        putStrLn'
            . unparseStrategy
            . Graph.lab'
            . Graph.context (Strategy.graph graph)
            $ node

    unparseStrategy :: StrategyPattern (CommonExpandedPattern level) -> String
    unparseStrategy =
        \case
            Bottom -> "Reached goal!"
            Stuck pat -> "Stuck: \n" <> unparseToString pat
            RewritePattern pat -> unparseToString pat

    indexNotFound :: String
    indexNotFound = "Variable or index not found"

    putStrLn' :: MonadIO m => String -> m ()
    putStrLn' = liftIO . putStrLn

unClaim :: forall level. Claim level -> RewriteRule level Kore.Variable
unClaim Claim { rule } = rule

unAxiom :: Axiom level -> RewriteRule level Kore.Variable
unAxiom (Axiom rule) = rule

emptyExecutionGraph
    :: Claim level
    -> Strategy.ExecutionGraph (StrategyPattern (CommonExpandedPattern level))
emptyExecutionGraph = Strategy.emptyExecutionGraph . extractConfig . unClaim

extractConfig
    :: RewriteRule level Kore.Variable
    -> StrategyPattern (CommonExpandedPattern level)
extractConfig (RewriteRule RulePattern { left, requires }) =
    RewritePattern $ Predicated left requires mempty
