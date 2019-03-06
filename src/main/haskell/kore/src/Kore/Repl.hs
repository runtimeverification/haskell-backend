{-|
Module      : Kore.Repl
Description : Logging functions.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
{-# LANGUAGE TemplateHaskell #-}

module Kore.Repl
    ( runRepl
    ) where

import           Control.Monad.Extra
                 ( loopM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( StateT )
import           Control.Monad.State.Strict
                 ( evalStateT, get )
import           Data.Functor
                 ( ($>) )
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Text
                 ( Text )
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( Parsec, many, parseMaybe, (<|>) )
import           Text.Megaparsec.Char
import           Text.Megaparsec.Char.Lexer
                 ( decimal )

import           Control.Error
                 ( atZ )
import           Control.Lens
                 ( (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import qualified Control.Lens.TH.Rules as Lens
import           Control.Monad.State.Strict
                 ( modify )
import           Control.Monad.State.Strict
                 ( lift )
import           Data.Bifunctor
                 ( first, second )
import           Data.List
                 ( intersperse )
import qualified Kore.AST.Common as Kore
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.MetaOrObject
                 ( Object )
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
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (..) )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule )
import           Kore.Step.AxiomPatterns
                 ( RulePattern (..) )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
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
import           Kore.Unparser
                 ( Unparse )

data Variable
    = forall a. Unparse a => Variable a
    | forall a. Unparse a => List [a]

type ExecutionGraph level = Strategy.ExecutionGraph (StrategyPattern (CommonExpandedPattern level))

data ReplState level = ReplState
    { variables :: Map String Variable
    , axioms    :: [Axiom level]
    , claims    :: [Claim level]
    , proving   :: Maybe (Claim level)
    , graph     :: Maybe (ExecutionGraph level)
    , node      :: Maybe (Graph.Node)
    , stepper   :: Claim level -> [Claim level] -> [Axiom level] -> ExecutionGraph level -> Graph.Node -> Simplifier (ExecutionGraph level)
    }

Lens.makeLenses ''ReplState

runRepl
    :: forall level
    .  MetaOrObject level
    => MetadataTools level StepperAttributes
    -> StepPatternSimplifier level Kore.Variable
    -> PredicateSubstitutionSimplifier level Simplifier
    -> [Axiom level]
    -> [Claim level]
    -> Simplifier ()
runRepl tools simplifier predicateSimplifier axioms claims
  = do
    replGreeting
    command <- maybe ShowUsage id . parseMaybe commandParser <$> prompt
    evalStateT (loopM repl0 command) state
  where
    state :: ReplState level
    state =
        ReplState
            ( Map.fromList
                [ ("axioms", List $ unAxiom <$> axioms)
                , ("claims", List $ unClaim <$> claims)
                ]
            )
            axioms
            claims
            Nothing
            Nothing
            Nothing
            (verifyClaimStep tools simplifier predicateSimplifier)

    unAxiom :: Axiom level -> RewriteRule level Kore.Variable
    unAxiom (Axiom rule) = rule

    repl0
        :: ReplCommand
        -> StateT (ReplState level) Simplifier (Either ReplCommand ())
    repl0 cmd = do
        continue <- replInterpreter cmd
        if continue
            then
                maybe
                    (Left ShowUsage)
                    Left
                    . parseMaybe commandParser <$> prompt
            else pure . pure $ ()

data ReplCommand
    = ShowUsage
    | Help
    | ShowVariables
    | ShowVariable !String
    | ShowArrayItem !String !Int
    | Prove !Int
    | ShowGraph
    | ProveStep
    | SelectNode !Int
    | ShowConfig
    | Exit

type Parser = Parsec String String

commandParser :: Parser ReplCommand
commandParser =
    help0
    <|> showVariables0
    <|> showVariable0
    <|> showArrayItem0
    <|> prove0
    <|> showGraph0
    <|> proveStep0
    <|> selectNode0
    <|> showConfig0
    <|> exit0
  where
    help0 :: Parser ReplCommand
    help0 = string "help" $> Help

    showVariable0 :: Parser ReplCommand
    showVariable0 =
        fmap ShowVariable $ string "show var" *> space *> many letterChar

    showVariables0 :: Parser ReplCommand
    showVariables0 = string "show vars" $> ShowVariables

    showGraph0 :: Parser ReplCommand
    showGraph0 = string "show graph" $> ShowGraph

    proveStep0 :: Parser ReplCommand
    proveStep0 = string "step" $> ProveStep

    selectNode0 :: Parser ReplCommand
    selectNode0 = fmap SelectNode $ string "select" *> space *> decimal

    showArrayItem0 :: Parser ReplCommand
    showArrayItem0 =
        ShowArrayItem
        <$> (string "show array" *> space *> many letterChar)
        <*> (space1 *> decimal)

    prove0 :: Parser ReplCommand
    prove0 = fmap Prove $ string "prove" *> space *> decimal

    showConfig0 :: Parser ReplCommand
    showConfig0 = string "show config" $> ShowConfig

    exit0 :: Parser ReplCommand
    exit0 = string "exit" $> Exit

replInterpreter
    :: forall level
    .  MetaOrObject level
    => ReplCommand
    -> StateT (ReplState level) Simplifier Bool
replInterpreter =
    \case
        ShowUsage -> showUsage0 $> True
        Help -> help0 $> True
        ShowVariables -> showVariables0 $> True
        ShowVariable var -> showVariable0 var $> True
        ShowArrayItem k i -> showArrayItem0 k i $> True
        Prove i -> prove0 i $> True
        ShowGraph -> showGraph0 $> True
        ProveStep -> proveStep0 $> True
        SelectNode i -> selectNode0 i $> True
        ShowConfig -> showConfig0 $> True
        Exit -> pure False
  where
    showUsage0 :: StateT st Simplifier ()
    showUsage0 = liftIO $ do
        putStrLn "usage!"

    help0 :: StateT st Simplifier ()
    help0 = liftIO $ do
        putStrLn "help!"

    showVariables0 :: StateT (ReplState level) Simplifier ()
    showVariables0 = do
        vars <- Map.keys . variables <$> get
        liftIO . putStrLn . concat . intersperse " " $ vars

    showVariable0 :: String -> StateT (ReplState level) Simplifier ()
    showVariable0 key = do
        var <- Map.lookup key . variables <$> get
        liftIO . putStrLn $ maybe "Not found" unparse' var


    showArrayItem0 :: String -> Int -> StateT (ReplState level) Simplifier ()
    showArrayItem0 key index = do
        var <- Map.lookup key . variables <$> get
        liftIO . putStrLn . maybe "Not found" unparse'
            $ var >>= toVariable index

    prove0 :: Int -> StateT (ReplState level) Simplifier ()
    prove0 index = do
        ReplState { claims } <- get
        case atZ claims index of
            Nothing -> liftIO $ putStrLn "Claim not found at index."
            Just claim -> do
                let
                    graph@Strategy.ExecutionGraph { root } = emptyExecutionGraph claim
                lensProving .= Just claim
                lensGraph .= Just graph
                lensNode .= Just root
                liftIO $ putStrLn "Execution Graph initiated"

    showGraph0 :: StateT (ReplState level) Simplifier ()
    showGraph0 = do
        ReplState { graph } <- get
        case graph of
            Nothing -> liftIO $ putStrLn "No proof in progress."
            Just Strategy.ExecutionGraph { graph } ->
                liftIO . Graph.prettyPrint . first (const ()) $ graph

    proveStep0 :: StateT (ReplState level) Simplifier ()
    proveStep0 = do
        ReplState { proving, claims, axioms, graph, node, stepper } <- get
        let
            graph0 = maybe (error "graph") id graph
            claim0 = maybe (error "claim") id proving
            node0  = maybe (error "node")  id node

        graph' <- lift
            $ stepper claim0 claims axioms graph0 node0
        lensGraph .= Just graph'
        liftIO $ putStrLn "Done!"

    selectNode0 :: Int -> StateT (ReplState level) Simplifier ()
    selectNode0 i = do
        ReplState { graph = graph' } <- get
        let
            Strategy.ExecutionGraph { graph } = maybe (error "graph") id graph'

        if i `elem` Graph.nodes graph && Graph.outdeg graph i == 0
            then lensNode .= Just i
            else liftIO $ putStrLn "Invalid node!"

    showConfig0 :: StateT (ReplState level) Simplifier ()
    showConfig0 = do
        ReplState { graph = graph' , node = node' } <- get
        let
            Strategy.ExecutionGraph { graph } = maybe (error "graph") id graph'
            node = maybe (error "node") id node'
            config = Graph.lab' $ Graph.context graph node

        liftIO . putStrLn . unparseStrategy $ config

    unparseStrategy :: StrategyPattern (CommonExpandedPattern level) -> String
    unparseStrategy =
        \case
            Bottom -> "#Bottom"
            Stuck pat -> "Stuck: \n" <> unparseToString pat
            RewritePattern pat -> unparseToString pat


    emptyExecutionGraph
        :: Claim level
        -> Strategy.ExecutionGraph (StrategyPattern (CommonExpandedPattern level))
    emptyExecutionGraph = Strategy.emptyExecutionGraph . extractConfig . unClaim

    extractConfig
        :: RewriteRule level Kore.Variable
        -> StrategyPattern (CommonExpandedPattern level)
    extractConfig (RewriteRule RulePattern { left, right, requires }) =
        RewritePattern $ Predicated left requires mempty

    claimsNotAvailable :: forall a. a
    claimsNotAvailable = error "Claims not available in state variables."

    toVariable :: Int -> Variable -> Maybe Variable
    toVariable index (List l) = Variable  <$> atZ l index
    toVariable _ _ = Nothing

    unparse' :: Variable -> String
    unparse' (Variable v) = unparseToString v
    unparse' (List l) = "length: " <> show (length l)

replGreeting :: MonadIO m => m ()
replGreeting =
    liftIO $ putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

unClaim :: forall level. Claim level -> RewriteRule level Kore.Variable
unClaim Claim { rule } = rule

prompt :: MonadIO m => m String
prompt = liftIO $ do
    putStr "Kore> "
    hFlush stdout
    getLine

showHelp :: IO ()
showHelp =
    putStrLn
        "Commands available from the prompt: \n\
        \help                shows this help message\n\
        \proof               shows the current proof\n\
        \go                  starts the automated prover"

showError :: IO ()
showError = putStrLn "\nUnknown command. Try 'help'."
