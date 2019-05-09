{-|
Module      : Kore.Repl.Data
Description : REPL data structures.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Repl.Data
    ( ReplCommand (..)
    , helpText
    , ExecutionGraph
    , AxiomIndex (..), ClaimIndex (..)
    , ReplNode (..)
    , ReplState (..)
    , NodeState (..)
    , AliasDefinition (..), ReplAlias (..), AliasArgument(..), AliasError (..)
    , getNodeState
    , InnerGraph
    , lensAxioms, lensClaims, lensClaim
    , lensGraph, lensNode, lensStepper
    , lensLabels, lensOmit, lensUnifier
    , lensCommands, lensAliases, shouldStore
    , UnifierWithExplanation (..)
    , runUnifierWithExplanation
    , emptyExecutionGraph
    , getClaimByIndex, getAxiomByIndex, getAxiomOrClaimByIndex
    , initializeProofFor
    , getTargetNode, getInnerGraph, getConfigAt, getRuleFor
    , StepResult(..), runStepper, runStepper'
    , updateInnerGraph
    , addOrUpdateAlias, findAlias, substituteAlias
    ) where

import           Control.Applicative
                 ( Alternative )
import           Control.Error
                 ( hush )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import qualified Control.Lens.TH.Rules as Lens
import           Control.Monad
                 ( join )
import           Control.Monad.Error.Class
                 ( MonadError )
import qualified Control.Monad.Error.Class as Monad.Error
import           Control.Monad.State.Strict
                 ( MonadState, get, modify )
import           Control.Monad.Trans.Accum
                 ( AccumT (AccumT), runAccumT )
import qualified Control.Monad.Trans.Accum as Monad.Accum
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Data.Bitraversable
                 ( bisequence, bitraverse )
import           Data.Coerce
                 ( coerce )
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Graph.Inductive.PatriciaTree
                 ( Gr )
import qualified Data.Map as Map
import           Data.Map.Strict
                 ( Map )
import           Data.Maybe
                 ( listToMaybe )
import           Data.Monoid
                 ( First (..) )
import           Data.Sequence
                 ( Seq )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Doc )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Exts
                 ( toList )
import           Numeric.Natural

import           Kore.Internal.Pattern
                 ( Conditional (..) )
import           Kore.Internal.TermLike
                 ( TermLike )
import           Kore.OnePath.StrategyPattern
import           Kore.OnePath.Verification
                 ( Axiom (..) )
import           Kore.OnePath.Verification
                 ( Claim )
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Syntax.Variable
                 ( Variable )
import           Kore.Unification.Unify
                 ( MonadUnify, Unifier )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( unparse )

newtype AxiomIndex = AxiomIndex
    { unAxiomIndex :: Int
    } deriving (Eq, Show)

newtype ClaimIndex = ClaimIndex
    { unClaimIndex :: Int
    } deriving (Eq, Show)

newtype ReplNode = ReplNode
    { unReplNode :: Graph.Node
    } deriving (Eq, Show)

data AliasDefinition = AliasDefinition
    { name      :: String
    , arguments :: [String]
    , command   :: String
    } deriving (Eq, Show)

data AliasArgument
  = SimpleArgument String
  | QuotedArgument String
  deriving (Eq, Show)

data ReplAlias = ReplAlias
    { name      :: String
    , arguments :: [AliasArgument]
    } deriving (Eq, Show)

-- | List of available commands for the Repl. Note that we are always in a proof
-- state. We pick the first available Claim when we initialize the state.
data ReplCommand
    = ShowUsage
    -- ^ This is the default action in case parsing all others fail.
    | Help
    -- ^ Shows the help message.
    | ShowClaim !ClaimIndex
    -- ^ Show the nth claim.
    | ShowAxiom !AxiomIndex
    -- ^ Show the nth axiom.
    | Prove !ClaimIndex
    -- ^ Drop the current proof state and re-initialize for the nth claim.
    | ShowGraph !(Maybe FilePath)
    -- ^ Show the current execution graph.
    | ProveSteps !Natural
    -- ^ Do n proof steps from current node.
    | ProveStepsF !Natural
    -- ^ Do n proof steps (through branchings) from the current node.
    | SelectNode !ReplNode
    -- ^ Select a different node in the graph.
    | ShowConfig !(Maybe ReplNode)
    -- ^ Show the configuration from the current node.
    | OmitCell !(Maybe String)
    -- ^ Adds or removes cell to omit list, or shows current omit list.
    | ShowLeafs
    -- ^ Show leafs which can continue evaluation and leafs which are stuck
    | ShowRule !(Maybe ReplNode)
    -- ^ Show the rule(s) that got us to this configuration.
    | ShowPrecBranch !(Maybe ReplNode)
    -- ^ Show the first preceding branch.
    | ShowChildren !(Maybe ReplNode)
    -- ^ Show direct children of node.
    | Label !(Maybe String)
    -- ^ Show all node labels or jump to a label.
    | LabelAdd !String !(Maybe ReplNode)
    -- ^ Add a label to a node.
    | LabelDel !String
    -- ^ Remove a label.
    | Redirect ReplCommand FilePath
    -- ^ Prints the output of the inner command to the file.
    | Try !(Either AxiomIndex ClaimIndex)
    -- ^ Attempt to apply axiom or claim to current node.
    | Clear !(Maybe ReplNode)
    -- ^ Remove child nodes from graph.
    | Pipe ReplCommand !String ![String]
    -- ^ Pipes a repl command into an external script.
    | SaveSession FilePath
    -- ^ Writes all commands executed in this session to a file on disk.
    | AppendTo ReplCommand FilePath
    -- ^ Appends the output of a command to a file.
    | Alias AliasDefinition
    -- ^ Alias a command.
    | TryAlias ReplAlias
    -- ^ Try running an alias.
    | LoadScript FilePath
    -- ^ Load script from file
    | Exit
    -- ^ Exit the repl.
    deriving (Eq, Show)

commandSet :: Set String
commandSet = Set.fromList
    [ "help"
    , "claim"
    , "axiom"
    , "prove"
    , "graph"
    , "step"
    , "stepf"
    , "select"
    , "omit"
    , "leafs"
    , "rule"
    , "prec-branch"
    , "children"
    , "label"
    , "try"
    , "clear"
    , "save-session"
    , "alias"
    , "load"
    , "exit"
    ]

-- | Please remember to update this text whenever you update the ADT above.
helpText :: String
helpText =
    "Available commands in the Kore REPL: \n\
    \help                                  shows this help message\n\
    \claim <n>                             shows the nth claim\n\
    \axiom <n>                             shows the nth axiom\n\
    \prove <n>                             initializes proof mode for the nth \
                                           \claim\n\
    \graph [file]                          shows the current proof graph (*)\n\
    \                                      (saves image if file argument is\
                                           \ given)\n\
    \step [n]                              attempts to run 'n' proof steps at\
                                           \the current node (n=1 by default)\n\
    \stepf [n]                             attempts to run 'n' proof steps at\
                                           \ the current node, stepping through\
                                           \ branchings (n=1 by default)\n\
    \select <n>                            select node id 'n' from the graph\n\
    \config [n]                            shows the config for node 'n'\
                                           \ (defaults to current node)\n\
    \omit [cell]                           adds or removes cell to omit list\
                                           \ (defaults to showing the omit\
                                           \ list)\n\
    \leafs                                 shows unevaluated or stuck leafs\n\
    \rule [n]                              shows the rule for node 'n'\
                                           \ (defaults to current node)\n\
    \prec-branch [n]                       shows first preceding branch\
                                           \ (defaults to current node)\n\
    \children [n]                          shows direct children of node\
                                           \ (defaults to current node)\n\
    \label                                 shows all node labels\n\
    \label <l>                             jump to a label\n\
    \label <+l> [n]                        add a new label for a node\
                                           \ (defaults to current node)\n\
    \label <-l>                            remove a label\n\
    \try <a|c><num>                        attempts <a>xiom or <c>laim at\
                                           \ index <num>.\n\
    \clear [n]                             removes all node children from the\
                                           \ proof graph\n\
    \                                      (defaults to current node)\n\
    \save-session file                     saves the current session to file\n\
    \alias <name> = <command>              adds as an alias for <command>\n\
    \<alias>                               runs an existing alias\n\
    \load file                             loads the file as a repl script\n\
    \exit                                  exits the repl\
    \\n\
    \Available modifiers:\n\
    \<command> > file                      prints the output of 'command'\
                                           \ to file\n\
    \<command> >> file                     appends the output of 'command'\
                                           \ to file\n\
    \<command> | external script           pipes command to external script\
                                           \ and prints the result in the\
                                           \ repl\n\
    \<command> | external script > file    pipes and then redirects the output\
                                           \ of the piped command to a file\n\
    \<command> | external script >> file   pipes and then appends the output\
                                           \ of the piped command to a file\n\
    \\n\
    \(*) If an edge is labeled as Simpl/RD it means that\
    \ either the target node was reached using the SMT solver\
    \ or it was reached through the Remove Destination step."

-- | Determines whether the command needs to be stored or not. Commands that
-- affect the outcome of the proof are stored.
shouldStore :: ReplCommand -> Bool
shouldStore =
    \case
        ShowUsage        -> False
        Help             -> False
        ShowClaim _      -> False
        ShowAxiom _      -> False
        ShowGraph _      -> False
        ShowConfig _     -> False
        ShowLeafs        -> False
        ShowRule _       -> False
        ShowPrecBranch _ -> False
        ShowChildren _   -> False
        SaveSession _    -> False
        Exit             -> False
        _                -> True

-- Type synonym for the actual type of the execution graph.
type ExecutionGraph =
    Strategy.ExecutionGraph
        (CommonStrategyPattern)
        (RewriteRule Variable)

type InnerGraph =
    Gr (CommonStrategyPattern) (Seq (RewriteRule Variable))

-- | State for the rep.
data ReplState claim = ReplState
    { axioms   :: [Axiom]
    -- ^ List of available axioms
    , claims   :: [claim]
    -- ^ List of claims to be proven
    , claim    :: claim
    -- ^ Currently focused claim in the repl
    , graph    :: ExecutionGraph
    -- ^ Execution graph for the current proof; initialized with root = claim
    , node     :: ReplNode
    -- ^ Currently selected node in the graph; initialized with node = root
    , commands :: Seq String
    -- ^ All commands evaluated by the current repl session
    -- TODO(Vladimir): This should be a Set String instead.
    , omit     :: [String]
    -- ^ The omit list, initially empty
    , stepper
        :: Claim claim
        => claim
        -> [claim]
        -> [Axiom]
        -> ExecutionGraph
        -> ReplNode
        -> Simplifier ExecutionGraph
    -- ^ Stepper function, it is a partially applied 'verifyClaimStep'
    , unifier
        :: TermLike Variable
        -> TermLike Variable
        -> UnifierWithExplanation ()
    -- ^ Unifier function, it is a partially applied 'unificationProcedure'
    --   where we discard the result since we are looking for unification
    --   failures
    , labels  :: Map String ReplNode
    -- ^ Map from labels to nodes
    , aliases :: Map String AliasDefinition
    -- ^ Map of command aliases
    }

-- | Unifier that stores the first 'explainBottom'.
-- See 'runUnifierWithExplanation'.
newtype UnifierWithExplanation a = UnifierWithExplanation
    { getUnifier :: AccumT (First (Doc ())) Unifier a
    } deriving (Alternative, Applicative, Functor, Monad)

instance MonadUnify UnifierWithExplanation where
    throwSubstitutionError =
        UnifierWithExplanation
            . Monad.Trans.lift
            . Monad.Unify.throwSubstitutionError

    throwUnificationError =
        UnifierWithExplanation
            . Monad.Trans.lift
            . Monad.Unify.throwUnificationError

    liftSimplifier =
        UnifierWithExplanation
            . Monad.Trans.lift
            . Monad.Unify.liftSimplifier

    liftBranchedSimplifier =
        UnifierWithExplanation
            . Monad.Trans.lift
            . Monad.Unify.liftBranchedSimplifier

    gather :: forall a . UnifierWithExplanation a -> UnifierWithExplanation [a]
    gather unifierWithExplanation =
        UnifierWithExplanation $ AccumT unifierActions
      where
        unifierAction :: First (Doc ()) -> Unifier (a, First (Doc ()))
        unifierAction w =
            runAccumT (getUnifier unifierWithExplanation) w

        unifierActions :: First (Doc ()) -> Unifier ([a], First (Doc ()))
        unifierActions w = do
            unifiersWithExplanations <- Monad.Unify.gather (unifierAction w)
            let
                (unifiers, explanations) = unzip unifiersWithExplanations
            return (unifiers, Foldable.fold explanations)

    scatter =
        UnifierWithExplanation . Monad.Trans.lift . Monad.Unify.scatter

    explainBottom info first second =
        UnifierWithExplanation . Monad.Accum.add . First . Just $ Pretty.vsep
            [ info
            , "When unifying:"
            , Pretty.indent 4 $ unparse first
            , "With:"
            , Pretty.indent 4 $ unparse second
            ]

runUnifierWithExplanation
    :: forall a
    .  UnifierWithExplanation a
    -> Simplifier (Maybe [Maybe (Doc ())])
runUnifierWithExplanation (UnifierWithExplanation accum)
  = fmap (fmap (map getFirst)) unificationExplanations
  where
    unificationResults :: Simplifier (Maybe [(a, First (Doc ()))])
    unificationResults =
        fmap hush
        $ Monad.Unify.runUnifier
        $ Monad.Accum.runAccumT accum mempty
    unificationExplanations :: Simplifier (Maybe [First (Doc ())])
    unificationExplanations =
        fmap (fmap (map snd)) unificationResults

Lens.makeLenses ''ReplState

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
    -> m (Maybe (Axiom))
getAxiomByIndex index = Lens.preuse $ lensAxioms . Lens.element index

-- | Transforms an axiom or claim index into an axiom or claim if they could be
-- found.
getAxiomOrClaimByIndex
    :: MonadState (ReplState claim) m
    => Either AxiomIndex ClaimIndex
    -> m (Maybe (Either (Axiom) claim))
getAxiomOrClaimByIndex =
    fmap bisequence
        . bitraverse
            (getAxiomByIndex . coerce)
            (getClaimByIndex . coerce)

-- | Initialize the execution graph with selected claim.
initializeProofFor
    :: MonadState (ReplState claim) m
    => Claim claim
    => claim
    -> m ()
initializeProofFor claim =
    modify (\st -> st
        { graph  = emptyExecutionGraph claim
        , claim  = claim
        , node   = ReplNode 0
        , labels = Map.empty
        })

-- | Get the internal representation of the execution graph.
getInnerGraph
    :: MonadState (ReplState claim) m
    => m InnerGraph
getInnerGraph = Strategy.graph . graph <$> get

-- | Update the internal representation of the execution graph.
updateInnerGraph
    :: MonadState (ReplState claim) m
    => InnerGraph
    -> m ()
updateInnerGraph ig = lensGraph Lens.%= updateInnerGraph0 ig
  where
    updateInnerGraph0 :: InnerGraph -> ExecutionGraph -> ExecutionGraph
    updateInnerGraph0 graph Strategy.ExecutionGraph { root } =
        Strategy.ExecutionGraph { root, graph }

-- | Get selected node (or current node for 'Nothing') and validate that it's
-- part of the execution graph.
getTargetNode
    :: MonadState (ReplState claim) m
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

-- | Result after running one or multiple proof steps.
data StepResult
    = NoResult
    -- ^ reached end of proof on current branch
    | SingleResult ReplNode
    -- ^ single follow-up configuration
    | BranchResult [ReplNode]
    -- ^ configuration branched
    deriving (Show)

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
    lensGraph Lens..= graph'
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
    ReplState { claim, graph, stepper } <- get
    gr@Strategy.ExecutionGraph { graph = innerGraph } <-
        Monad.Trans.lift $ stepper claim claims axioms graph node
    pure . (,) gr $ case Graph.suc innerGraph (unReplNode node) of
        []       -> NoResult
        [single] -> case getNodeState innerGraph single of
                        Nothing -> NoResult
                        Just (StuckNode, _) -> NoResult
                        _ -> SingleResult . ReplNode $ single
        nodes    -> BranchResult $ fmap ReplNode nodes

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

data NodeState = StuckNode | UnevaluatedNode
    deriving (Eq, Ord, Show)

data AliasError
    = NameAlreadyDefined
    | UnknownCommand

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
