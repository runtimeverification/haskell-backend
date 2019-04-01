{-|
Module      : Kore.Interpreter
Description : REPL interpreter
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Interpreter
    ( replInterpreter
    , emptyExecutionGraph
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Control.Lens
                 ( (%=), (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad.Extra
                 ( loop, loopM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( MonadState, StateT )
import           Data.Foldable
                 ( traverse_ )
import           Data.Functor
                 ( ($>) )
import qualified Data.Functor.Foldable as Recursive
import           Data.Graph.Inductive.Graph
                 ( Graph )
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.GraphViz as Graph
import           Data.List.Extra
                 ( groupSort )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( catMaybes )
import qualified Data.Text as Text
import           Data.Text.Prettyprint.Doc
                 ( pretty )

import           Kore.AST.Common
                 ( Application (..), Pattern (..), SymbolOrAlias (..),
                 Variable )
import qualified Kore.AST.Identifier as Identifier
                 ( Id (..) )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.Attribute.Axiom
                 ( SourceLocation (..) )
import qualified Kore.Attribute.Axiom as Attribute
                 ( sourceLocation )
import           Kore.OnePath.Step
                 ( CommonStrategyPattern, StrategyPattern (..),
                 strategyPattern )
import           Kore.OnePath.Verification
                 ( Axiom (..) )
import           Kore.OnePath.Verification
                 ( Claim (..) )
import           Kore.Repl.Data
import           Kore.Step.Pattern
                 ( StepPattern )
import           Kore.Step.Representation.ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.Rule
                 ( RewriteRule (..) )
import           Kore.Step.Rule
                 ( RulePattern (..) )
import qualified Kore.Step.Rule as Axiom
                 ( attributes )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Unparser
                 ( unparseToString )

-- | Interprets a REPL command in a stateful Simplifier context.
replInterpreter
    :: forall level
    .  MetaOrObject level
    => ReplCommand
    -> StateT (ReplState level) Simplifier Bool
replInterpreter =
    \case
        ShowUsage         -> showUsage         $> True
        Help              -> help              $> True
        ShowClaim c       -> showClaim c       $> True
        ShowAxiom a       -> showAxiom a       $> True
        Prove i           -> prove i           $> True
        ShowGraph         -> showGraph         $> True
        ProveSteps n      -> proveSteps n      $> True
        SelectNode i      -> selectNode i      $> True
        ShowConfig mc     -> showConfig mc     $> True
        OmitCell c        -> omitCell c        $> True
        ShowLeafs         -> showLeafs         $> True
        ShowPrecBranch mn -> showPrecBranch mn $> True
        ShowChildren mn   -> showChildren mn   $> True
        ShowLabels        -> showLabels        $> True
        SetLabel l n      -> setLabel l n      $> True
        GotoLabel l       -> gotoLabel l       $> True
        RemoveLabel l     -> removeLabel l     $> True
        Exit              -> pure                 False

showUsage :: MonadIO m => m ()
showUsage =
    putStrLn' "Could not parse command, try using 'help'."

help :: MonadIO m => m ()
help = putStrLn' helpText

showClaim
    :: MonadIO m
    => MonadState (ReplState level) m
    => Int
    -> m ()
showClaim index = do
    claim <- Lens.preuse $ lensClaims . Lens.element index
    maybe printNotFound (printRewriteRule . unClaim) $ claim

showAxiom
    :: MonadIO m
    => MonadState (ReplState level) m
    => Int
    -> m ()
showAxiom index = do
    axiom <- Lens.preuse $ lensAxioms . Lens.element index
    maybe printNotFound (printRewriteRule . unAxiom) $ axiom

prove
    :: MonadIO m
    => MonadState (ReplState level) m
    => Int
    -> m ()
prove index = do
    claim' <- Lens.preuse $ lensClaims . Lens.element index
    case claim' of
        Nothing -> printNotFound
        Just claim -> do
            let
                graph@Strategy.ExecutionGraph { root }
                    = emptyExecutionGraph claim
            lensGraph  .= graph
            lensClaim  .= claim
            lensNode   .= root
            lensLabels .= Map.empty
            putStrLn' "Execution Graph initiated"

showGraph
    :: MonadIO m
    => MonadState (ReplState level) m
    => m ()
showGraph = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    liftIO $ showDotGraph graph

proveSteps :: Int -> StateT (ReplState level) Simplifier ()
proveSteps n = do
    result <- loopM performStepNoBranching (n, Success)
    case result of
        (0, Success) -> pure ()
        (done, res) ->
            putStrLn'
                $ "Stopped after "
                <> show (n - done - 1)
                <> " step(s) due to "
                <> show res

selectNode :: Int -> StateT (ReplState level) Simplifier ()
selectNode i = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    if i `elem` Graph.nodes graph
        then lensNode .= i
        else putStrLn' "Invalid node!"

showConfig
    :: MetaOrObject level
    => Maybe Int
    -> StateT (ReplState level) Simplifier ()
showConfig configNode = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id configNode
    if node' `elem` Graph.nodes graph
        then do
            omit <- Lens.use lensOmit
            putStrLn' $ "Config at node " <> show node' <> " is:"
            putStrLn'
                . unparseStrategy omit
                . Graph.lab'
                . Graph.context graph
                $ node'
        else putStrLn' "Invalid node!"

omitCell :: Maybe String -> StateT (ReplState level) Simplifier ()
omitCell =
    \case
        Nothing  -> showCells
        Just str -> addOrRemove str
  where
    showCells :: StateT (ReplState level) Simplifier ()
    showCells = Lens.use lensOmit >>= traverse_ putStrLn'

    addOrRemove :: String -> StateT (ReplState level) Simplifier ()
    addOrRemove str = lensOmit %= toggle str

    toggle :: String -> [String] -> [String]
    toggle x xs
      | x `elem` xs = filter (/= x) xs
      | otherwise   = x : xs

data NodeStates = StuckNode | UnevaluatedNode
    deriving (Eq, Ord, Show)

showLeafs
    :: MetaOrObject level
    => StateT (ReplState level) Simplifier ()
showLeafs = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    let nodes = Graph.nodes graph
    let leafs = filter (\x -> (Graph.outdeg graph x) == 0) nodes
    let result =
            groupSort
                . catMaybes
                . fmap (getNodeState graph)
                $ leafs

    putStrLn' $ foldr ((<>) . showPair) "" result
  where
    getNodeState graph node =
        maybe Nothing (\x -> Just (x, node))
        . strategyPattern (const . Just $ UnevaluatedNode) (const . Just $ StuckNode) Nothing
        . Graph.lab'
        . Graph.context graph
        $ node

    showPair :: (NodeStates, [Graph.Node]) -> String
    showPair (ns, xs) = show ns <> ": " <> show xs

showPrecBranch
    :: Maybe Int
    -> StateT (ReplState level) Simplifier ()
showPrecBranch mnode = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id mnode
    if node' `elem` Graph.nodes graph
       then putStrLn' . show $ loop (loopCond graph) node'
       else putStrLn' "Invalid node!"
  where
    loopCond gph n
      | (Graph.outdeg gph n) <= 1 && (not . null . Graph.pre gph $ n)
          = Left $ head (Graph.pre gph n)
      | otherwise = Right n

showChildren
    :: Maybe Int
    -> StateT (ReplState level) Simplifier ()
showChildren mnode = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id mnode
    if node' `elem` Graph.nodes graph
       then putStrLn' $ show (Graph.suc graph node')
       else putStrLn' "Invalid node!"

showLabels :: StateT (ReplState level) Simplifier ()
showLabels = do
    labels <- Lens.use lensLabels
    if null labels
       then putStrLn' "No labels are set."
       else putStrLn' $ Map.foldrWithKey acc "Labels: " labels
  where
    acc :: String -> Graph.Node -> String -> String
    acc key node res =
        res <> "\n  " <> key <> ": " <> (show node)

setLabel
    :: String
    -> Int
    -> StateT (ReplState level) Simplifier ()
setLabel label node = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    labels <- Lens.use lensLabels
    if label `Map.notMember` labels && node `elem` Graph.nodes graph
       then do
           lensLabels .= Map.insert label node labels
           putStrLn' "Label added."
       else putStrLn' "Label already exists or the node isn't in the graph."

gotoLabel :: String -> StateT (ReplState level) Simplifier ()
gotoLabel label = do
    labels <- Lens.use lensLabels
    selectNode $ maybe (-1) id (Map.lookup label labels)

removeLabel :: String -> StateT (ReplState level) Simplifier ()
removeLabel label = do
    labels <- Lens.use lensLabels
    if label `Map.member` labels
       then do
           lensLabels .= Map.delete label labels
           putStrLn' "Removed label."
       else putStrLn' "Label doesn't exist."

printRewriteRule :: MonadIO m => RewriteRule level Variable -> m ()
printRewriteRule rule = do
    putStrLn' $ unparseToString rule
    putStrLn'
        . show
        . pretty
        . extractSourceAndLocation
        $ rule

performSingleStep
    :: StateT (ReplState level) Simplifier StepResult
performSingleStep = do
    f <- Lens.use lensStepper
    node <- Lens.use lensNode
    res <- f
    if res
        then do
            Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
            let
                context = Graph.context graph node
            case Graph.suc' context of
                [] -> pure NoChildNodes
                [configNo] -> do
                    lensNode .= configNo
                    pure Success
                neighbors -> pure (Branch neighbors)
        else pure NodeAlreadyEvaluated

-- | Performs n proof steps, picking the next node unless branching occurs.
-- Returns 'Left' while it has to continue looping, and 'Right' when done
-- or when execution branches or proof finishes earlier than the counter.
--
-- See 'loopM' for details.
performStepNoBranching
    :: (Int, StepResult)
    -- ^ (current step, last result)
    -> StateT
        (ReplState level)
        Simplifier
            (Either
                    (Int, StepResult)
                    (Int, StepResult)
            )
performStepNoBranching (0, res) =
    pure $ Right (0, res)
performStepNoBranching (n, Success) = do
    res <- performSingleStep
    pure $ Left (n-1, res)
performStepNoBranching (n, res) =
    pure $ Right (n, res)

unparseStrategy
    :: forall level
    .  MetaOrObject level
    => [String]
    -> CommonStrategyPattern level
    -> String
unparseStrategy omitList =
    strategyPattern
        (\pat -> unparseToString (hide <$> pat))
        (\pat -> "Stuck: \n" <> unparseToString (hide <$> pat))
        "Reached bottom"
  where
    hide :: StepPattern level Variable -> StepPattern level Variable
    hide =
        Recursive.unfold $ \stepPattern ->
            case Recursive.project stepPattern of
                ann :< ApplicationPattern app
                  | shouldBeExcluded (applicationSymbolOrAlias app) ->
                    -- Do not display children
                    ann :< ApplicationPattern (withoutChildren app)
                projected -> projected
      where
        withoutChildren app = app { applicationChildren = [] }

    shouldBeExcluded =
       (flip elem) omitList
           . Text.unpack
           . Identifier.getId
           . symbolOrAliasConstructor

extractSourceAndLocation
    :: RewriteRule level Variable
    -> SourceLocation
extractSourceAndLocation
    (RewriteRule (RulePattern{ Axiom.attributes })) =
        Attribute.sourceLocation attributes

printNotFound :: MonadIO m => m ()
printNotFound = putStrLn' "Variable or index not found"

putStrLn' :: MonadIO m => String -> m ()
putStrLn' = liftIO . putStrLn

showDotGraph :: Graph gr => gr nl el -> IO ()
showDotGraph =
    (flip Graph.runGraphvizCanvas') Graph.Xlib
        . Graph.graphToDot Graph.nonClusteredParams

data StepResult
    = NodeAlreadyEvaluated
    | NoChildNodes
    | Branch [Graph.Node]
    | Success
    deriving Show

unClaim :: forall level. Claim level -> RewriteRule level Variable
unClaim Claim { rule } = rule

unAxiom :: Axiom level -> RewriteRule level Variable
unAxiom (Axiom rule) = rule

emptyExecutionGraph
    :: Claim level
    -> Strategy.ExecutionGraph (CommonStrategyPattern level)
emptyExecutionGraph = Strategy.emptyExecutionGraph . extractConfig . unClaim

extractConfig
    :: RewriteRule level Variable
    -> CommonStrategyPattern level
extractConfig (RewriteRule RulePattern { left, requires }) =
    RewritePattern $ Predicated left requires mempty
