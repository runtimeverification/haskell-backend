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
    , getInternalIdentifier
    , getAxiomByName, getClaimByName, getAxiomOrClaimByName
    , getClaimIndexByName, getNameText
    , ruleReference
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
    , appReplOut
    , replOut, replOutputToString
    )
    where

import Control.Concurrent.MVar
import qualified Control.Lens as Lens hiding
    ( makeLenses
    )
import Control.Monad.Error.Class
    ( MonadError
    )
import qualified Control.Monad.Error.Class as Monad.Error
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import Control.Monad.State.Strict
    ( MonadState
    , get
    , modify
    )
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Bifunctor as Bifunctor
import Data.Bitraversable
    ( bisequence
    , bitraverse
    )
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Default as Default
import Data.Foldable
    ( find
    )
import Data.Generics.Product
import qualified Data.Graph.Inductive.Graph as Graph
import Data.List.Extra
    ( findIndex
    , groupSort
    )
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.Map as Map
import Data.Map.Strict
    ( Map
    )
import Data.Maybe
import Data.Sequence
    ( Seq
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    , unpack
    )
import GHC.Exts
    ( toList
    )
import System.IO
    ( Handle
    , IOMode (AppendMode)
    , hClose
    , openFile
    )

import Control.Monad.Reader
    ( MonadReader
    , asks
    )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Label as AttrLabel
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern
    ( toTermLike
    )
import qualified Kore.Internal.Predicate as IPredicate
import Kore.Internal.TermLike
    ( Sort
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Logger.Output as Logger
import Kore.Predicate.Predicate as Predicate
import Kore.Repl.Data
import Kore.Step.Rule
    ( RewriteRule (..)
    , RulePattern (..)
    )
import Kore.Step.Rule as Rule
import Kore.Step.Simplification.Data
    ( MonadSimplify
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Strategies.Goal
import Kore.Strategies.ProofState
    ( ProofState (Goal)
    , ProofStateTransformer (ProofStateTransformer)
    , proofState
    )
import qualified Kore.Strategies.ProofState as ProofState.DoNotUse
import Kore.Strategies.Verification
import Kore.Syntax.Variable
    ( Variable
    )

-- | Creates a fresh execution graph for the given claim.
emptyExecutionGraph
    :: Claim claim
    => axiom ~ Rule claim
    => claim -> ExecutionGraph axiom
emptyExecutionGraph =
    Strategy.emptyExecutionGraph . extractConfig . RewriteRule . coerce
  where
    extractConfig
        :: RewriteRule Variable
        -> CommonProofState
    extractConfig (RewriteRule RulePattern { left, requires }) =
        Goal $ Conditional left requires mempty

ruleReference
    :: (Either AxiomIndex ClaimIndex -> a)
    -> (RuleName -> a)
    -> RuleReference
    -> a
ruleReference f g ref =
    case ref of
        ByIndex axiomOrClaimIndex ->
            f axiomOrClaimIndex
        ByName ruleName ->
            g ruleName

-- | Get nth claim from the claims list.
getClaimByIndex
    :: MonadState (ReplState claim) m
    => Int
    -- ^ index in the claims list
    -> m (Maybe claim)
getClaimByIndex index = Lens.preuse $ field @"claims" . Lens.element index

-- | Get nth axiom from the axioms list.
getAxiomByIndex
    :: MonadState (ReplState claim) m
    => Int
    -- ^ index in the axioms list
    -> m (Maybe (Rule claim))
getAxiomByIndex index = Lens.preuse $ field @"axioms" . Lens.element index

-- | Get the leftmost axiom with a specific name from the axioms list.
getAxiomByName
    :: MonadState (ReplState claim) m
    => axiom ~ Rule claim
    => Coercible axiom (RulePattern Variable)
    => Coercible (RulePattern Variable) axiom
    => String
    -- ^ label attribute
    -> m (Maybe axiom)
getAxiomByName name = do
    axioms <- Lens.use (field @"axioms")
    return $ find (isNameEqual name) axioms

-- | Get the leftmost claim with a specific name from the claim list.
getClaimByName
    :: MonadState (ReplState claim) m
    => Claim claim
    => String
    -- ^ label attribute
    -> m (Maybe claim)
getClaimByName name = do
    claims <- Lens.use (field @"claims")
    return $ find (isNameEqual name) claims

getClaimIndexByName
    :: MonadState (ReplState claim) m
    => Claim claim
    => String
    -- ^ label attribute
    -> m (Maybe ClaimIndex)
getClaimIndexByName name= do
    claims <- Lens.use (field @"claims")
    return $ ClaimIndex <$> findIndex (isNameEqual name) claims

getAxiomOrClaimByName
    :: MonadState (ReplState claim) m
    => Claim claim
    => axiom ~ Rule claim
    => RuleName
    -> m (Maybe (Either axiom claim))
getAxiomOrClaimByName (RuleName name) = do
    mAxiom <- getAxiomByName name
    case mAxiom of
        Nothing -> do
            mClaim <- getClaimByName name
            case mClaim of
                Nothing -> return Nothing
                Just claim ->
                    return . Just . Right $ claim
        Just axiom ->
            return . Just . Left $ axiom

isNameEqual
    :: Coercible rule (RulePattern Variable)
    => String -> rule -> Bool
isNameEqual name rule =
    maybe
        False
        ( (== name) . unpack)
          (AttrLabel.unLabel
          . getNameText
          $ rule
        )

getNameText
    :: Coercible rule (RulePattern Variable)
    => rule -> AttrLabel.Label
getNameText =
    Attribute.label
    . attributes
    . coerce

-- | Transforms an axiom or claim index into an axiom or claim if they could be
-- found.
getAxiomOrClaimByIndex
    :: MonadState (ReplState claim) m
    => axiom ~ Rule claim
    => Either AxiomIndex ClaimIndex
    -> m (Maybe (Either axiom claim))
getAxiomOrClaimByIndex =
    fmap bisequence
        . bitraverse
            (getAxiomByIndex . coerce)
            (getClaimByIndex . coerce)

getInternalIdentifier
    :: Coercible rule (RulePattern Variable)
    => rule -> Attribute.RuleIndex
getInternalIdentifier =
    Attribute.identifier
    . Rule.attributes
    . coerce

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
    => axiom ~ Rule claim
    => Claim claim
    => m (InnerGraph axiom)
getInnerGraph =
    fmap Strategy.graph getExecutionGraph

-- | Get the current execution graph
getExecutionGraph
    :: MonadState (ReplState claim) m
    => axiom ~ Rule claim
    => Claim claim
    => m (ExecutionGraph axiom)
getExecutionGraph = do
    ReplState { claimIndex, graphs, claim } <- get
    let mgraph = Map.lookup claimIndex graphs
    return $ fromMaybe (emptyExecutionGraph claim) mgraph

-- | Update the internal representation of the current execution graph.
updateInnerGraph
    :: forall claim axiom m
    .  MonadState (ReplState claim) m
    => axiom ~ Rule claim
    => InnerGraph axiom
    -> m ()
updateInnerGraph ig = do
    ReplState { claimIndex, graphs } <- get
    field @"graphs" Lens..=
        Map.adjust (updateInnerGraph0 ig) claimIndex graphs
  where
    updateInnerGraph0
        :: InnerGraph axiom
        -> ExecutionGraph axiom
        -> ExecutionGraph axiom
    updateInnerGraph0 graph Strategy.ExecutionGraph { root } =
        Strategy.ExecutionGraph { root, graph }

-- | Update the current execution graph.
updateExecutionGraph
    :: MonadState (ReplState claim) m
    => axiom ~ Rule claim
    => ExecutionGraph axiom
    -> m ()
updateExecutionGraph gph = do
    ReplState { claimIndex, graphs } <- get
    field @"graphs" Lens..= Map.insert claimIndex gph graphs

-- | Get the node labels for the current claim.
getLabels
    :: MonadState (ReplState claim) m
    => m (Map String ReplNode)
getLabels = do
    ReplState { claimIndex, labels } <- get
    let mlabels = Map.lookup claimIndex labels
    return $ fromMaybe Map.empty mlabels

-- | Update the node labels for the current claim.
setLabels
    :: MonadState (ReplState claim) m
    => Map String ReplNode
    -> m ()
setLabels lbls = do
    ReplState { claimIndex, labels } <- get
    field @"labels" Lens..= Map.insert claimIndex lbls labels


-- | Get selected node (or current node for 'Nothing') and validate that it's
-- part of the execution graph.
getTargetNode
    :: MonadState (ReplState claim) m
    => Claim claim
    => Maybe ReplNode
    -- ^ node index
    -> m (Maybe ReplNode)
getTargetNode maybeNode = do
    currentNode <- Lens.use (field @"node")
    let node' = unReplNode $ fromMaybe currentNode maybeNode
    graph <- getInnerGraph
    if node' `elem` Graph.nodes graph
       then pure . Just . ReplNode $ node'
       else pure Nothing

-- | Get the configuration at selected node (or current node for 'Nothing').
getConfigAt
    :: MonadState (ReplState claim) m
    => Claim claim
    => Maybe ReplNode
    -> m (Maybe (ReplNode, CommonProofState))
getConfigAt maybeNode = do
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> pure Nothing
        Just n -> do
            graph' <- getInnerGraph
            pure $ Just (n, getLabel graph' (unReplNode n))
  where
    getLabel gr n = Graph.lab' . Graph.context gr $ n

-- | Get the rule used to reach selected node.
getRuleFor
    :: MonadState (ReplState claim) m
    => axiom ~ Rule claim
    => Claim claim
    => Maybe ReplNode
    -- ^ node index
    -> m (Maybe axiom)
getRuleFor maybeNode = do
    targetNode <- getTargetNode maybeNode
    graph' <- getInnerGraph
    pure $ fmap unReplNode targetNode >>= getRewriteRule . Graph.inn graph'
  where
    getRewriteRule
        :: [(a, b, Seq axiom)]
        -> Maybe axiom
    getRewriteRule = listToMaybe . concatMap (toList . third)

    third :: forall a b c. (a, b, c) -> c
    third (_, _, c) = c

-- | Lifting function that takes logging into account.
liftSimplifierWithLogger
    :: forall a t m claim
    .  MonadState (ReplState claim) (t m)
    => MonadSimplify m
    => MonadIO m
    => Monad.Trans.MonadTrans t
    => MVar (Logger.LogAction IO Logger.SomeEntry)
    -> m a
    -> t m a
liftSimplifierWithLogger mLogger simplifier = do
    (severity, logScope, logType) <- logging <$> get
    (textLogger, maybeHandle) <- logTypeToLogger logType
    let scopes = unLogScope logScope
        logger = Logger.makeKoreLogger severity scopes textLogger
    _ <- Monad.Trans.lift . liftIO $ swapMVar mLogger logger
    result <- Monad.Trans.lift simplifier
    maybe (pure ()) (Monad.Trans.lift . liftIO . hClose) maybeHandle
    pure result
  where
    logTypeToLogger
        :: LogType
        -> t m (Logger.LogAction IO Text, Maybe Handle)
    logTypeToLogger =
        \case
            NoLogging   -> pure (mempty, Nothing)
            LogToStdOut -> pure (Logger.logTextStderr, Nothing)
            LogToFile file -> do
                handle <- Monad.Trans.lift . liftIO $ openFile file AppendMode
                pure (Logger.logTextHandle handle, Just handle)

-- | Run a single step for the data in state
-- (claim, axioms, claims, current node and execution graph).
runStepper
    :: MonadState (ReplState claim) (t m)
    => MonadReader (Config claim m) (t m)
    => Monad.Trans.MonadTrans t
    => MonadSimplify m
    => MonadIO m
    => Claim claim
    => t m StepResult
runStepper = do
    ReplState { claims, axioms, node } <- get
    (graph', res) <- runStepper' claims axioms node
    updateExecutionGraph graph'
    case res of
        SingleResult nextNode -> do
            field @"node" Lens..= nextNode
            pure res
        _                     -> pure res

-- | Run a single step for the current claim with the selected claims, axioms
-- starting at the selected node.
runStepper'
    :: MonadState (ReplState claim) (t m)
    => MonadReader (Config claim m) (t m)
    => axiom ~ Rule claim
    => Monad.Trans.MonadTrans t
    => MonadSimplify m
    => MonadIO m
    => Claim claim
    => [claim]
    -> [axiom]
    -> ReplNode
    -> t m (ExecutionGraph axiom, StepResult)
runStepper' claims axioms node = do
    ReplState { claim } <- get
    stepper <- asks stepper
    mvar <- asks logger
    gph <- getExecutionGraph
    gr@Strategy.ExecutionGraph { graph = innerGraph } <-
        liftSimplifierWithLogger mvar $ stepper claim claims axioms gph node
    pure . (,) gr
        $ case Graph.suc innerGraph (unReplNode node) of
            []       -> NoResult
            [single] ->
                case getNodeState innerGraph single of
                    Nothing -> NoResult
                    Just (StuckNode, _) -> NoResult
                    _ -> SingleResult . ReplNode $ single
            nodes -> BranchResult $ fmap ReplNode nodes

runUnifier
    :: MonadState (ReplState claim) (t m)
    => MonadReader (Config claim m) (t m)
    => Monad.Trans.MonadTrans t
    => MonadSimplify m
    => MonadIO m
    => TermLike Variable
    -> TermLike Variable
    -> t m (Either ReplOutput (NonEmpty (IPredicate.Predicate Variable)))
runUnifier first second = do
    unifier <- asks unifier
    mvar <- asks logger
    liftSimplifierWithLogger mvar
        . runUnifierWithExplanation
        $ unifier first second

getNodeState :: InnerGraph axiom -> Graph.Node -> Maybe (NodeState, Graph.Node)
getNodeState graph node =
        fmap (\nodeState -> (nodeState, node))
        . proofState ProofStateTransformer
            { goalTransformer = const . Just $ UnevaluatedNode
            , goalRemainderTransformer = const . Just $ StuckNode
            , goalRewrittenTransformer = const . Just $ UnevaluatedNode
            , provenValue = Nothing
            }
        . Graph.lab'
        . Graph.context graph
        $ node

nodeToPattern
    :: InnerGraph axiom
    -> Graph.Node
    -> Maybe (TermLike Variable)
nodeToPattern graph node =
    proofState ProofStateTransformer
        { goalTransformer = Just . toTermLike
        , goalRemainderTransformer = Just . toTermLike
        , goalRewrittenTransformer = Just . toTermLike
        , provenValue = Nothing
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
    field @"aliases" Lens.%= Map.insert name alias
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
        <$> Lens.use (field @"aliases")

    falseToError :: AliasError -> Bool -> m ()
    falseToError e b =
        if b then pure () else Monad.Error.throwError e


findAlias
    :: MonadState (ReplState claim) m
    => String
    -> m (Maybe AliasDefinition)
findAlias name = Map.lookup name <$> Lens.use (field @"aliases")

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
        , antiLeft = Nothing
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
    => axiom ~ Rule claim
    => MonadState (ReplState claim) m
    => m [Rule.OnePathRule Variable]
generateInProgressOPClaims = do
    graphs <- Lens.use (field @"graphs")
    claims <- Lens.use (field @"claims")
    let started = startedOPClaims graphs claims
        notStarted = notStartedOPClaims graphs claims
    return $ started <> notStarted
  where
    startedOPClaims
        :: Claim claim
        => Map.Map ClaimIndex (ExecutionGraph axiom)
        -> [claim]
        -> [Rule.OnePathRule Variable]
    startedOPClaims graphs claims =
        fmap createOnePathClaim
        $ claimsWithPatterns graphs claims
        >>= sequence
    notStartedOPClaims
        :: Claim claim
        => Map.Map ClaimIndex (ExecutionGraph axiom)
        -> [claim]
        -> [Rule.OnePathRule Variable]
    notStartedOPClaims graphs claims =
        Rule.OnePathRule
        . coerce
        <$> filter (not . isTrusted)
                ( (claims !!)
                . unClaimIndex
                <$> Set.toList
                    (Set.difference
                        ( Set.fromList
                        $ fmap ClaimIndex [0..length claims - 1]
                        )
                        ( Set.fromList
                        $ Map.keys graphs
                        )
                    )
                )

claimsWithPatterns
    :: Map ClaimIndex (ExecutionGraph axiom)
    -> [claim]
    -> [(claim, [TermLike Variable])]
claimsWithPatterns graphs claims =
    Bifunctor.bimap
        ((claims !!) . unClaimIndex)
        (findTerminalPatterns . Strategy.graph)
    <$> Map.toList graphs

findTerminalPatterns
    :: InnerGraph axiom
    -> [TermLike Variable]
findTerminalPatterns graph =
    mapMaybe (nodeToPattern graph)
    . findLeafNodes
    $ graph

currentClaimSort
    :: Claim claim
    => MonadState (ReplState claim) m
    => m Sort
currentClaimSort = do
    claims <- Lens.use (field @"claim")
    return . TermLike.termLikeSort
        . Rule.onePathRuleToPattern
        . Rule.OnePathRule
        . coerce
        $ claims

sortLeafsByType :: InnerGraph axiom -> Map.Map NodeState [Graph.Node]
sortLeafsByType graph =
    Map.fromList
        . groupSort
        . mapMaybe (getNodeState graph)
        . findLeafNodes
        $ graph


findLeafNodes :: InnerGraph axiom -> [Graph.Node]
findLeafNodes graph =
    filter ((==) 0 . Graph.outdeg graph) $ Graph.nodes graph

appReplOut :: ReplOut -> ReplOutput -> ReplOutput
appReplOut rout routput = routput <> ReplOutput [rout]

replOut
    :: (String -> a)
    -> (String -> a)
    -> ReplOut
    -> a
replOut f g =
    \case
        AuxOut str  -> f str
        KoreOut str -> g str

replOutputToString :: ReplOutput -> String
replOutputToString (ReplOutput out) =
    out >>= replOut id id
