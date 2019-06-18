{-|
Module      : Kore.Repl.Data
Description : REPL data structures.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.State
    ( emptyExecutionGraph
    , getClaimByIndex, getAxiomByIndex, getAxiomOrClaimByIndex
    , switchToProof
    , getTargetNode, getInnerGraph, getExecutionGraph
    , getConfigAt, getRuleFor, getLabels, setLabels
    , runStepper, runStepper'
    , runUnifier
    , updateInnerGraph, updateExecutionGraph
    , addOrUpdateAlias, findAlias, substituteAlias
    , sortLeafsByType
    , generateInProgressOPClaims
    , currentClaimSort
    , conjOfOnePathClaims
    )
    where

import           Control.Concurrent.MVar
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( join )
import           Control.Monad.Error.Class
                 ( MonadError )
import qualified Control.Monad.Error.Class as Monad.Error
import           Control.Monad.IO.Class
                 ( liftIO )
import           Control.Monad.State.Strict
                 ( MonadState, get, modify )
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Bifunctor as Bifunctor
import           Data.Bitraversable
                 ( bisequence, bitraverse )
import           Data.Coerce
                 ( coerce )
import qualified Data.Default as Default
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.List.Extra
                 ( groupSort )
import           Data.List.NonEmpty
                 ( NonEmpty (..) )
import qualified Data.Map as Map
import           Data.Map.Strict
                 ( Map )
import           Data.Maybe
                 ( catMaybes, listToMaybe )
import           Data.Sequence
                 ( Seq )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           Data.Text.Prettyprint.Doc
                 ( Doc )
import           GHC.Exts
                 ( toList )
import           System.IO
                 ( Handle, IOMode (AppendMode), hClose, openFile )

import           Kore.Internal.Conditional
                 ( Conditional (..) )
import           Kore.Internal.Pattern
                 ( toTermLike )
import qualified Kore.Internal.Predicate as IPredicate
import           Kore.Internal.TermLike
                 ( Sort, TermLike )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Logger.Output as Logger
import           Kore.OnePath.StrategyPattern
import           Kore.OnePath.Verification
                 ( Axiom (..), Claim )
import           Kore.Predicate.Predicate as Predicate
import           Kore.Repl.Data
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (..) )
import           Kore.Step.Rule as Rule
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Syntax.Variable
                 ( Variable )

-- | Creates a fresh execution graph for the given claim.
emptyExecutionGraph :: Claim claim => claim -> ExecutionGraph
emptyExecutionGraph =
    Strategy.emptyExecutionGraph . extractConfig . RewriteRule . coerce
  where
    extractConfig
        :: RewriteRule Variable
        -> CommonStrategyPattern
    extractConfig (RewriteRule RulePattern { left, requires }) =
        RewritePattern $ Conditional left requires mempty

-- | Get nth claim from the claims list.
getClaimByIndex
    :: MonadState (ReplState claim) m
    => Int
    -- ^ index in the claims list
    -> m (Maybe claim)
getClaimByIndex index = Lens.preuse $ lensClaims . Lens.element index

-- | Get nth axiom from the axioms list.
getAxiomByIndex
    :: MonadState (ReplState claim) m
    => Int
    -- ^ index in the axioms list
    -> m (Maybe Axiom)
getAxiomByIndex index = Lens.preuse $ lensAxioms . Lens.element index

-- | Transforms an axiom or claim index into an axiom or claim if they could be
-- found.
getAxiomOrClaimByIndex
    :: MonadState (ReplState claim) m
    => Either AxiomIndex ClaimIndex
    -> m (Maybe (Either Axiom claim))
getAxiomOrClaimByIndex =
    fmap bisequence
        . bitraverse
            (getAxiomByIndex . coerce)
            (getClaimByIndex . coerce)

-- | Update the currently selected claim to prove.
switchToProof
    :: MonadState (ReplState claim) m
    => Claim claim
    => claim
    -> ClaimIndex
    -> m ()
switchToProof claim cindex =
    modify (\st -> st
        { claim = claim
        , claimIndex = cindex
        , node = ReplNode 0
        })

-- | Get the internal representation of the execution graph.
getInnerGraph
    :: MonadState (ReplState claim) m
    => Claim claim
    => m InnerGraph
getInnerGraph =
    fmap Strategy.graph getExecutionGraph

-- | Get the current execution graph
getExecutionGraph
    :: MonadState (ReplState claim) m
    => Claim claim
    => m ExecutionGraph
getExecutionGraph = do
    ReplState { claimIndex, graphs, claim } <- get
    let mgraph = Map.lookup claimIndex graphs
    return $ maybe (emptyExecutionGraph claim) id mgraph

-- | Update the internal representation of the current execution graph.
updateInnerGraph
    :: MonadState (ReplState claim) m
    => InnerGraph
    -> m ()
updateInnerGraph ig = do
    ReplState { claimIndex, graphs } <- get
    lensGraphs Lens..=
        Map.adjust (updateInnerGraph0 ig) claimIndex graphs
  where
    updateInnerGraph0 :: InnerGraph -> ExecutionGraph -> ExecutionGraph
    updateInnerGraph0 graph Strategy.ExecutionGraph { root } =
        Strategy.ExecutionGraph { root, graph }

-- | Update the current execution graph.
updateExecutionGraph
    :: MonadState (ReplState claim) m
    => ExecutionGraph
    -> m ()
updateExecutionGraph gph = do
    ReplState { claimIndex, graphs } <- get
    lensGraphs Lens..= Map.insert claimIndex gph graphs

-- | Get the node labels for the current claim.
getLabels
    :: MonadState (ReplState claim) m
    => m (Map String ReplNode)
getLabels = do
    ReplState { claimIndex, labels } <- get
    let mlabels = Map.lookup claimIndex labels
    return $ maybe Map.empty id mlabels

-- | Update the node labels for the current claim.
setLabels
    :: MonadState (ReplState claim) m
    => Map String ReplNode
    -> m ()
setLabels lbls = do
    ReplState { claimIndex, labels } <- get
    lensLabels Lens..= Map.insert claimIndex lbls labels


-- | Get selected node (or current node for 'Nothing') and validate that it's
-- part of the execution graph.
getTargetNode
    :: MonadState (ReplState claim) m
    => Claim claim
    => Maybe ReplNode
    -- ^ node index
    -> m (Maybe ReplNode)
getTargetNode maybeNode = do
    currentNode <- Lens.use lensNode
    let node' = unReplNode $ maybe currentNode id maybeNode
    graph <- getInnerGraph
    if node' `elem` Graph.nodes graph
       then pure . Just . ReplNode $ node'
       else pure $ Nothing

-- | Get the configuration at selected node (or current node for 'Nothing').
getConfigAt
    :: MonadState (ReplState claim) m
    => Claim claim
    => Maybe ReplNode
    -> m (Maybe (ReplNode, CommonStrategyPattern))
getConfigAt maybeNode = do
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> pure $ Nothing
        Just n -> do
            graph' <- getInnerGraph
            pure $ Just (n, getLabel graph' (unReplNode n))
  where
    getLabel gr n = Graph.lab' . Graph.context gr $ n

-- | Get the rule used to reach selected node.
getRuleFor
    :: MonadState (ReplState claim) m
    => Claim claim
    => Maybe ReplNode
    -- ^ node index
    -> m (Maybe (RewriteRule Variable))
getRuleFor maybeNode = do
    targetNode <- getTargetNode maybeNode
    graph' <- getInnerGraph
    pure $ fmap unReplNode targetNode >>= getRewriteRule . Graph.inn graph'
  where
    getRewriteRule
        :: forall a b
        .  [(a, b, Seq (RewriteRule Variable))]
        -> Maybe (RewriteRule Variable)
    getRewriteRule =
        listToMaybe
        . join
        . fmap (toList . third)

    third :: forall a b c. (a, b, c) -> c
    third (_, _, c) = c

-- | Lifting function that takes logging into account.
liftSimplifierWithLogger
    :: forall a t claim
    .  MonadState (ReplState claim) (t Simplifier)
    => Monad.Trans.MonadTrans t
    => MVar (Logger.LogAction IO Logger.LogMessage)
    -> Simplifier a
    -> t Simplifier a
liftSimplifierWithLogger mLogger simplifier = do
   (severity, logType) <- logging <$> get
   (textLogger, maybeHandle) <- logTypeToLogger logType
   let logger = Logger.makeKoreLogger severity textLogger
   _ <- Monad.Trans.lift . liftIO $ swapMVar mLogger logger
   result <- Monad.Trans.lift simplifier
   maybe (pure ()) (Monad.Trans.lift . liftIO . hClose) maybeHandle
   pure result
  where
    logTypeToLogger
        :: LogType
        -> t Simplifier (Logger.LogAction IO Text, Maybe Handle)
    logTypeToLogger =
        \case
            NoLogging   -> pure (mempty, Nothing)
            LogToStdOut -> pure (Logger.logTextStdout, Nothing)
            LogToFile file -> do
                handle <- Monad.Trans.lift . liftIO $ openFile file AppendMode
                pure (Logger.logTextHandle handle, Just handle)

-- | Run a single step for the data in state
-- (claim, axioms, claims, current node and execution graph).
runStepper
    :: MonadState (ReplState claim) (m Simplifier)
    => Monad.Trans.MonadTrans m
    => Claim claim
    => m Simplifier StepResult
runStepper = do
    ReplState { claims, axioms, node } <- get
    (graph', res) <- runStepper' claims axioms node
    updateExecutionGraph graph'
    case res of
        SingleResult nextNode -> do
            lensNode Lens..= nextNode
            pure res
        _                     -> pure res

-- | Run a single step for the current claim with the selected claims, axioms
-- starting at the selected node.
runStepper'
    :: MonadState (ReplState claim) (m Simplifier)
    => Monad.Trans.MonadTrans m
    => Claim claim
    => [claim]
    -> [Axiom]
    -> ReplNode
    -> m Simplifier (ExecutionGraph, StepResult)
runStepper' claims axioms node = do
    ReplState { claim, stepper } <- get
    mvar <- Lens.use lensLogger
    gph <- getExecutionGraph
    gr@Strategy.ExecutionGraph { graph = innerGraph } <-
        liftSimplifierWithLogger mvar $ stepper claim claims axioms gph node
    pure . (,) gr $ case Graph.suc innerGraph (unReplNode node) of
        []       -> NoResult
        [single] -> case getNodeState innerGraph single of
                        Nothing -> NoResult
                        Just (StuckNode, _) -> NoResult
                        _ -> SingleResult . ReplNode $ single
        nodes    -> BranchResult $ fmap ReplNode nodes

runUnifier
    :: MonadState (ReplState claim) (m Simplifier)
    => Monad.Trans.MonadTrans m
    => TermLike Variable
    -> TermLike Variable
    -> m Simplifier (Either (Doc ()) (NonEmpty (IPredicate.Predicate Variable)))
runUnifier first second = do
    unifier <- Lens.use lensUnifier
    mvar <- Lens.use lensLogger
    liftSimplifierWithLogger mvar
        . runUnifierWithExplanation
        $ unifier first second

getNodeState :: InnerGraph -> Graph.Node -> Maybe (NodeState, Graph.Node)
getNodeState graph node =
        fmap (\nodeState -> (nodeState, node))
        . strategyPattern StrategyPatternTransformer
            { rewriteTransformer = const . Just $ UnevaluatedNode
            , stuckTransformer = const . Just $ StuckNode
            , bottomValue = Nothing
            }
        . Graph.lab'
        . Graph.context graph
        $ node

nodeToPattern
    :: InnerGraph
    -> Graph.Node
    -> Maybe (TermLike Variable)
nodeToPattern graph node =
    strategyPattern StrategyPatternTransformer
        { rewriteTransformer = Just . toTermLike
        , stuckTransformer = Just . toTermLike
        , bottomValue = Nothing
        }
    . Graph.lab'
    . Graph.context graph
    $ node

-- | Adds or updates the provided alias.
addOrUpdateAlias
    :: forall m claim
    .  MonadState (ReplState claim) m
    => MonadError AliasError m
    => AliasDefinition
    -> m ()
addOrUpdateAlias alias@AliasDefinition { name, command } = do
    checkNameIsNotUsed
    checkCommandExists
    lensAliases Lens.%= Map.insert name alias
  where
    checkNameIsNotUsed :: m ()
    checkNameIsNotUsed =
        not . Set.member name <$> existingCommands
            >>= falseToError NameAlreadyDefined

    checkCommandExists :: m ()
    checkCommandExists = do
        cmds <- existingCommands
        let
            maybeCommand = listToMaybe $ words command
            maybeExists = Set.member <$> maybeCommand <*> pure cmds
        maybe
            (Monad.Error.throwError UnknownCommand)
            (falseToError UnknownCommand)
            maybeExists

    existingCommands :: m (Set String)
    existingCommands =
        Set.union commandSet
        . Set.fromList
        . Map.keys
        <$> Lens.use lensAliases

    falseToError :: AliasError -> Bool -> m ()
    falseToError e b =
        if b then pure () else Monad.Error.throwError e


findAlias
    :: MonadState (ReplState claim) m
    => String
    -> m (Maybe AliasDefinition)
findAlias name = Map.lookup name <$> Lens.use lensAliases

substituteAlias
    :: AliasDefinition
    -> ReplAlias
    -> String
substituteAlias
    AliasDefinition { arguments, command }
    ReplAlias { arguments = actualArguments } =
    unwords
      . fmap replaceArguments
      . words
      $ command
  where
    values :: Map String AliasArgument
    values
      | length arguments == length actualArguments
        = Map.fromList $ zip arguments actualArguments
      | otherwise = Map.empty

    replaceArguments :: String -> String
    replaceArguments s = maybe s toString $ Map.lookup s values

    toString :: AliasArgument -> String
    toString = \case
        SimpleArgument str -> str
        QuotedArgument str -> "\"" <> str <> "\""

createOnePathClaim
    :: Claim claim
    => (claim, TermLike Variable)
    -> Rule.OnePathRule Variable
createOnePathClaim (claim, cpattern) =
    Rule.OnePathRule
    $ Rule.RulePattern
        { left = cpattern
        , right = Rule.right . coerce $ claim
        , requires = Predicate.makeTruePredicate
        , ensures = Rule.ensures . coerce $ claim
        , attributes = Default.def
        }

conjOfOnePathClaims
    :: [Rule.OnePathRule Variable]
    -> Sort
    -> TermLike Variable
conjOfOnePathClaims claims sort =
    foldr
        TermLike.mkAnd
        (TermLike.mkTop sort)
        $ fmap Rule.onePathRuleToPattern claims

generateInProgressOPClaims
    :: Claim claim
    => MonadState (ReplState claim) m
    => m [Rule.OnePathRule Variable]
generateInProgressOPClaims = do
    graphs <- Lens.use lensGraphs
    claims <- Lens.use lensClaims
    let started = startedOPClaims graphs claims
        notStarted = notStartedOPClaims graphs claims
    return $ started <> notStarted
  where
    startedOPClaims
        :: Claim claim
        => Map.Map ClaimIndex ExecutionGraph
        -> [claim]
        -> [Rule.OnePathRule Variable]
    startedOPClaims graphs claims =
        fmap createOnePathClaim
        $ claimsWithPatterns graphs claims
        >>= sequence
    notStartedOPClaims
        :: Claim claim
        => Map.Map ClaimIndex ExecutionGraph
        -> [claim]
        -> [Rule.OnePathRule Variable]
    notStartedOPClaims graphs claims =
        Rule.OnePathRule
        . coerce
        . (claims !!)
        . unClaimIndex
        <$> (Set.toList $ Set.difference
                (Set.fromList $ fmap ClaimIndex [0..length claims - 1])
                (Set.fromList $ Map.keys graphs)
            )

claimsWithPatterns
    :: Map ClaimIndex ExecutionGraph
    -> [claim]
    -> [(claim, [TermLike Variable])]
claimsWithPatterns graphs claims =
    Bifunctor.bimap
        ((claims !!) . unClaimIndex)
        (findTerminalPatterns . Strategy.graph)
    <$> (Map.toList graphs)

findTerminalPatterns
    :: InnerGraph
    -> [TermLike Variable]
findTerminalPatterns graph =
    catMaybes
    . fmap (nodeToPattern graph)
    . findLeafNodes
    $ graph

currentClaimSort
    :: Claim claim
    => MonadState (ReplState claim) m
    => m Sort
currentClaimSort = do
    claims <- Lens.use lensClaim
    return . TermLike.termLikeSort
        . Rule.onePathRuleToPattern
        . Rule.OnePathRule
        . coerce
        $ claims

sortLeafsByType :: InnerGraph -> Map.Map NodeState [Graph.Node]
sortLeafsByType graph =
    Map.fromList
        . groupSort
        . catMaybes
        . fmap (getNodeState graph)
        . findLeafNodes
        $ graph


findLeafNodes :: InnerGraph -> [Graph.Node]
findLeafNodes graph =
    filter ((==) 0 . Graph.outdeg graph) $ Graph.nodes graph
