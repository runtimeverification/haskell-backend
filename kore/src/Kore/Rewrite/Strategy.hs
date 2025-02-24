{- |
Module      : Kore.Rewrite.Strategy
Description : Strategies for pattern rewriting
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
This module should be imported qualified to avoid collisions with "Prelude":
@
import Kore.Rewrite.Strategy ( Strategy )
import Kore.Rewrite.Strategy qualified as Strategy
@
-}
module Kore.Rewrite.Strategy (
    -- * Step, a.k.a Strategy
    Step,

    -- * Running strategies
    unfoldSearchOrder,
    unfoldTransition,
    GraphSearchOrder (..),
    FinalNodeType (..),
    ExecutionGraph (..),
    insNode,
    insEdge,
    runStrategy,
    runStrategyWithSearchOrder,
    pickLongest,
    pickFinal,
    pickOne,
    pickStar,
    pickPlus,
    assert,
    transitionRule,
    executionHistoryStep,
    emptyExecutionGraph,
    module Kore.Rewrite.Transition,
    LimitExceeded (..),
) where

import Control.Lens qualified as Lens
import Control.Monad (
    foldM,
    (>=>),
 )
import Control.Monad.Catch (
    Exception (..),
    MonadThrow,
 )
import Control.Monad.Catch qualified as Exception
import Control.Monad.State.Strict (
    MonadState,
 )
import Control.Monad.State.Strict qualified as State
import Data.Generics.Product (
    field,
 )
import Data.Graph.Inductive.Graph qualified as Graph
import Data.Graph.Inductive.PatriciaTree (
    Gr,
 )
import Data.Limit (
    Limit (..),
    withinLimit,
 )
import Data.List qualified as List
import Data.Maybe (
    fromJust,
 )
import Data.Sequence qualified as Seq
import GHC.Generics qualified as GHC
import Kore.Rewrite.Transition
import Numeric.Natural
import Prelude.Kore

-- | A "step" (aka "strategy") is a sequence of primitive actions
type Step action = [action]

data ExecutionGraph config rule = ExecutionGraph
    { root :: Graph.Node
    , graph :: Gr config (Seq rule)
    }
    deriving stock (Eq, Show)
    deriving stock (GHC.Generic)

{- | A temporary data structure used to construct the 'ExecutionGraph'.
 Well, it was intended to be temporary, but for the purpose of making
 'pickLongest' fast it turns out to be useful to keep it around.
-}
data ChildNode config rule = ChildNode
    { config :: config
    , parents :: [(Seq rule, Graph.Node)]
    -- ^ The predecessor configurations in the execution graph and the sequence
    -- of rules applied from the parent configuration to the present
    -- configuration.
    }
    deriving stock (Eq, Show, Functor)

{- | Insert a node into the execution graph.

The 'Graph.Node' index must not already exist in the graph.
-}
insNode ::
    (Graph.Node, config) ->
    ExecutionGraph config rule ->
    ExecutionGraph config rule
insNode lnode exe@ExecutionGraph{graph} =
    exe{graph = Graph.insNode lnode graph}

{- | Insert an unlabeled edge into the execution graph.

The source and target 'Graph.Node' indices must already exist in the graph.
-}
insEdge ::
    -- | (source, target) of the edge
    (Graph.Node, Graph.Node) ->
    ExecutionGraph config rule ->
    ExecutionGraph config rule
insEdge (fromNode, toNode) exe@ExecutionGraph{graph} =
    exe{graph = Graph.insEdge (fromNode, toNode, mempty) graph}

insChildNode ::
    MonadState (Gr config (Seq rule)) m =>
    ChildNode config rule ->
    m Graph.Node
insChildNode configNode =
    State.state insChildNodeWorker
  where
    ChildNode{config} = configNode
    ChildNode{parents} = configNode
    insChildNodeWorker graph =
        let node' = (succ . snd) (Graph.nodeRange graph)
            lnode = (node', config)
            ledges = do
                (edge, node) <- parents
                return (node, node', edge)
            graph' = Graph.insEdges ledges $ Graph.insNode lnode graph
         in (node', graph')

{- | Perform a single step in the execution starting from the selected node in
 the graph and returning the resulting graph. Note that this does *NOT* do
 state merging, not even at the same level. The node ID's are also not
 hashes but just regular integer ID's.

 Using simple ID's for nodes will likely be changed in the future in order to
 allow merging of states, loop detection, etc.
-}
executionHistoryStep ::
    forall m config rule prim.
    Monad m =>
    -- | Transition rule
    (prim -> config -> TransitionT rule m config) ->
    -- | Primitive strategy
    [prim] ->
    -- | execution graph so far
    ExecutionGraph config rule ->
    -- | current "selected" node
    Graph.Node ->
    -- | graph with one more step executed for the selected node
    m (ExecutionGraph config rule)
executionHistoryStep transit step exe@ExecutionGraph{graph} node
    | nodeIsNotLeaf = error "Node has already been evaluated"
    | otherwise =
        case Graph.lab graph node of
            Nothing -> error "Node does not exist"
            Just config -> do
                configs <- runTransitionT (transitionRule transit step config)
                let nodes = mkChildNode <$> configs
                    graph' =
                        State.execState
                            (traverse_ insChildNode nodes)
                            graph
                pure $ exe{graph = graph'}
  where
    nodeIsNotLeaf :: Bool
    nodeIsNotLeaf = Graph.outdeg graph node > 0

    mkChildNode ::
        -- Child node identifier and configuration
        (config, Seq rule) ->
        ChildNode config rule
    mkChildNode (config, rules) =
        ChildNode
            { config
            , parents = [(rules, node)]
            }

{- | Create a default/empty execution graph for the provided configuration. Note
 that the ID of the root node is NOT a hash but rather just '0'.

 Using simple ID's for nodes will likely be changed in the future in order to
 allow merging of states, loop detection, etc.
-}
emptyExecutionGraph ::
    forall config rule.
    config ->
    ExecutionGraph config rule
emptyExecutionGraph config =
    ExecutionGraph
        { root = 0
        , graph = Graph.insNode (0, config) Graph.empty
        }

-- | Search order of the execution graph.
data GraphSearchOrder = BreadthFirst | DepthFirst deriving stock (Eq)

newtype LimitExceeded a = LimitExceeded (Seq a)
    deriving stock (Show, Typeable)

instance (Show a, Typeable a) => Exception (LimitExceeded a)

data FinalNodeType = Leaf | LeafOrBranching deriving stock (Eq)

updateGraph ::
    forall instr config rule m.
    MonadState (ExecutionGraph config rule) m =>
    (instr -> config -> TransitionT rule m config) ->
    ([instr], Graph.Node) ->
    m [([instr], Graph.Node)]
updateGraph _ ([], _) = return []
updateGraph transit (instr : instrs, node) = do
    config <- getConfig node
    transitions <- runTransitionT (transit instr config)
    nodes <- traverse (insTransition node) transitions
    pure ((,) instrs <$> nodes)

getConfig ::
    MonadState (ExecutionGraph config rule) m =>
    Graph.Node ->
    m config
getConfig node = do
    graph <- Lens.use (field @"graph")
    pure $ fromMaybe (error "Node does not exist") (Graph.lab graph node)

insTransition ::
    MonadState (ExecutionGraph config rule) m =>
    -- | parent node
    Graph.Node ->
    (config, Seq rule) ->
    m Graph.Node
insTransition node (config, rules) = do
    graph <- Lens.use (field @"graph")
    let node' = (succ . snd) (Graph.nodeRange graph)
    Lens.modifying (field @"graph") $ Graph.insNode (node', config)
    Lens.modifying (field @"graph") $ Graph.insEdges [(node, node', rules)]
    pure node'

{- | Execute a 'Strategy'.

 The primitive strategy rule is used to execute the 'apply' strategy. The
 primitive rule is considered successful if it returns any children and
 considered failed if it returns no children.

 The strategies are applied in sequence. An edge @a -> b@ exists between
 two configurations @a, b@ if @b@ follows by applying one step of the strategy
 to @a@.
 Nondeterministic strategies result in nodes with an outdegree > 1.
 If two different branches converge to the same configuration at the same time
 step, they will be recombined, yielding a node with indegree > 1.

See also: 'pickLongest', 'pickFinal', 'pickOne', 'pickStar', 'pickPlus'
-}
constructExecutionGraph ::
    forall m config rule instr.
    MonadThrow m =>
    Limit Natural ->
    (instr -> config -> TransitionT rule m config) ->
    [instr] ->
    GraphSearchOrder ->
    config ->
    m (ExecutionGraph config rule)
constructExecutionGraph breadthLimit transit instrs0 searchOrder0 config0 =
    unfoldM_ mkQueue transit' (instrs0, root execGraph)
        & flip State.execStateT execGraph
  where
    execGraph = emptyExecutionGraph config0
    dropStrategy = snd

    mkQueue = \as ->
        unfoldSearchOrder searchOrder0 as
            >=> applyBreadthLimit breadthLimit dropStrategy

    transit' =
        updateGraph $ \instr config ->
            mapTransitionT lift $ transit instr config

{- | Unfold the function from the initial vertex.

@unfoldM_@ visits (perform an effect on) every descendant in the graph.

The queue updating function should be 'unfoldBreadthFirst' or
'unfoldDepthFirst', optionally composed with 'applyBreadthLimit'.
-}
unfoldM_ ::
    forall m a.
    Monad m =>
    -- | queue updating function
    ([a] -> Seq a -> m (Seq a)) ->
    -- | unfolding function
    (a -> m [a]) ->
    -- | initial vertex
    a ->
    m ()
unfoldM_ mkQueue next = \a ->
    mkQueue [a] Seq.empty >>= worker
  where
    worker Seq.Empty = return ()
    worker (a Seq.:<| as) = do
        as' <- next a
        mkQueue as' as >>= worker

unfoldBreadthFirst :: Applicative f => [a] -> Seq a -> f (Seq a)
unfoldBreadthFirst as' as = pure (as <> Seq.fromList as')

unfoldDepthFirst :: Applicative f => [a] -> Seq a -> f (Seq a)
unfoldDepthFirst as' as = pure (Seq.fromList as' <> as)

unfoldSearchOrder ::
    Applicative f =>
    GraphSearchOrder ->
    [a] ->
    Seq a ->
    f (Seq a)
unfoldSearchOrder DepthFirst = unfoldDepthFirst
unfoldSearchOrder BreadthFirst = unfoldBreadthFirst

applyBreadthLimit ::
    Exception (LimitExceeded b) =>
    MonadThrow m =>
    Limit Natural ->
    (a -> b) ->
    Seq a ->
    m (Seq a)
applyBreadthLimit breadthLimit transf as
    | exceedsLimit as =
        Exception.throwM (LimitExceeded (transf <$> as))
    | otherwise = pure as
  where
    exceedsLimit = not . withinLimit breadthLimit . fromIntegral . Seq.length

{- | Turn a transition rule into an unfolding function.

@unfoldTransition@ applies the transition rule to the first @instr@ and threads
the tail of the list to the results. The result is @[]@ if the @[instr]@ is
empty.
-}
unfoldTransition ::
    Monad m =>
    -- | transition rule
    (instr -> config -> m [config]) ->
    ([instr], config) ->
    m [([instr], config)]
unfoldTransition transit (instrs, config) =
    case instrs of
        [] -> pure []
        instr : instrs' -> do
            configs' <- transit instr config
            pure ((,) instrs' <$> configs')

-- | Transition rule for running a 'Strategy'.
transitionRule ::
    -- | Primitive strategy rule
    (prim -> config -> TransitionT rule m config) ->
    ([prim] -> config -> TransitionT rule m config)
transitionRule applyPrim prims config =
    foldM (flip applyPrim) config prims

{- | Execute a 'Strategy'.

The primitive strategy rule is used to execute the 'apply' strategy. The
primitive rule is considered successful if it returns any children and
considered failed if it returns no children.

The strategies are applied in sequence. The 'rootLabel' of is the initial
configuration and the 'subForest' are the children returned by the first
strategy in the list; the tree is unfolded likewise by recursion.

See also: 'pickLongest', 'pickFinal', 'pickOne', 'pickStar', 'pickPlus'
-}
runStrategy ::
    forall m prim rule config.
    MonadThrow m =>
    Limit Natural ->
    -- | Primitive strategy rule
    (prim -> config -> TransitionT rule m config) ->
    -- | Steps
    [Step prim] ->
    -- | Initial configuration
    config ->
    m (ExecutionGraph config rule)
runStrategy breadthLimit applyPrim steps config0 =
    runStrategyWithSearchOrder breadthLimit applyPrim steps BreadthFirst config0

runStrategyWithSearchOrder ::
    forall m prim rule config.
    MonadThrow m =>
    Limit Natural ->
    -- | Primitive strategy rule
    (prim -> config -> TransitionT rule m config) ->
    -- | Steps
    [Step prim] ->
    -- | Search order of the execution graph
    GraphSearchOrder ->
    -- | Initial configuration
    config ->
    m (ExecutionGraph config rule)
runStrategyWithSearchOrder breadthLimit applyPrim steps searchOrder0 config0 =
    constructExecutionGraph
        breadthLimit
        (transitionRule applyPrim)
        steps
        searchOrder0
        config0

{- | Construct the step-wise execution history of an 'ExecutionGraph'.

The step-wise execution history is the list of configurations at each time step.
-}
history :: ExecutionGraph config rule -> [[config]]
history ExecutionGraph{root, graph} =
    List.unfoldr history1 [root]
  where
    history1 [] = Nothing
    history1 nodes = Just (labs, concatMap (Graph.suc graph) nodes)
      where
        -- Node labels at this level. Using fromJust is safe because these
        -- nodes were just retrieved from the graph; if they have suddenly
        -- disappeared, something has gone tragically wrong.
        labs = fromJust . Graph.lab graph <$> nodes

{- | Pick the longest-running branch from a 'Tree'.

See also: 'runStrategy'
-}
pickLongest :: ExecutionGraph config rule -> config
pickLongest exeGraph = (last $ history exeGraph) !! 0

-- | Return all 'stuck' configurations, i.e. all leaves of the 'Tree'.
pickFinal :: ExecutionGraph config rule -> [config]
pickFinal ExecutionGraph{graph} =
    map (fromJust . Graph.lab graph) $
        filter isFinal $
            Graph.nodes graph
  where
    isFinal = (0 ==) . Graph.outdeg graph

-- | Return all configurations reachable in one step.
pickOne :: ExecutionGraph config rule -> [config]
pickOne ExecutionGraph{root, graph} =
    map (fromJust . Graph.lab graph) $
        Graph.neighbors graph root

-- | Return all reachable configurations.
pickStar :: ExecutionGraph config rule -> [config]
pickStar ExecutionGraph{graph} = map snd $ Graph.labNodes graph

-- | Return all configurations reachable after at least one step.
pickPlus :: ExecutionGraph config rule -> [config]
pickPlus ExecutionGraph{root, graph} =
    map snd $
        filter ((/= root) . fst) $
            Graph.labNodes graph
