{- |
Module      : Kore.Step.Strategy
Description : Strategies for pattern rewriting
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
This module should be imported qualified to avoid collisions with "Prelude":
@
import Kore.Step.Strategy ( Strategy )
import qualified Kore.Step.Strategy as Strategy
@
-}
module Kore.Step.Strategy (
    -- * Strategies
    Strategy (..),
    and,
    all,
    or,
    try,
    first,
    any,
    many,
    some,
    apply,
    seq,
    sequence,
    stuck,
    continue,

    -- * Running strategies
    leavesM,
    unfoldM_,
    applyBreadthLimit,
    unfoldBreadthFirst,
    unfoldDepthFirst,
    unfoldSearchOrder,
    unfoldTransition,
    GraphSearchOrder (..),
    constructExecutionGraph,
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
    module Kore.Step.Transition,
    LimitExceeded (..),
) where

import Control.Error (
    maybeT,
 )
import qualified Control.Lens as Lens
import Control.Monad (
    guard,
    (>=>),
 )
import Control.Monad.Catch (
    Exception (..),
    MonadThrow,
 )
import qualified Control.Monad.Catch as Exception
import Control.Monad.State.Strict (
    MonadState,
 )
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product (
    field,
 )
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree (
    Gr,
 )
import Data.Limit (
    Limit (..),
    withinLimit,
 )
import qualified Data.List as List
import Data.Maybe (
    fromJust,
 )
import qualified Data.Sequence as Seq
import qualified GHC.Generics as GHC
import Kore.Step.Transition
import Numeric.Natural
import Prelude.Kore hiding (
    all,
    and,
    any,
    many,
    or,
    seq,
    sequence,
    some,
 )

{- | An execution strategy.

    @Strategy prim@ represents a strategy for execution by applying rewrite
    axioms of type @prim@.
-}

-- TODO (thomas.tuegel): This could be implemented as an algebra so that a
-- strategy is a free monad over the primitive rule type and the result of
-- execution is not a generic tree, but a cofree comonad with exactly the
-- branching structure described by the strategy algebra.
data Strategy prim where
    -- The recursive arguments of these constructors are /intentionally/ lazy to
    -- allow strategies to loop.

    -- | Apply two strategies in sequence.
    Seq :: Strategy prim -> Strategy prim -> Strategy prim
    -- | Apply both strategies to the same configuration, i.e. in parallel.
    And :: Strategy prim -> Strategy prim -> Strategy prim
    -- | Apply the second strategy if the first fails to produce children.
    Or :: Strategy prim -> Strategy prim -> Strategy prim
    -- | Apply the rewrite rule, then advance to the next strategy.
    Apply :: !prim -> Strategy prim
    -- | @Stuck@ produces no children.
    Stuck :: Strategy prim
    -- | @Continue@ produces one child identical to its parent.
    Continue :: Strategy prim
    deriving stock (Eq, Show, Functor)

{- | Apply two strategies in sequence.

The first strategy is applied, then the second is applied to all the children of
the first.
-}
seq :: Strategy prim -> Strategy prim -> Strategy prim
seq = Seq

{- | Apply all of the strategies in sequence.

@
sequence [] === continue
@
-}
sequence :: [Strategy prim] -> Strategy prim
sequence = foldr seq continue

-- | Apply both strategies to the same configuration, i.e. in parallel.
and :: Strategy prim -> Strategy prim -> Strategy prim
and = And

{- | Apply all of the strategies in parallel.

@
all [] === stuck
@
-}
all :: [Strategy prim] -> Strategy prim
all = foldr and stuck

{- | Apply the second strategy if the first fails immediately.

A strategy is considered successful if it produces any children.
-}
or :: Strategy prim -> Strategy prim -> Strategy prim
or = Or

{- | Apply the given strategies in order until one succeeds.

A strategy is considered successful if it produces any children.

@
any [] === stuck
@
-}
first :: [Strategy prim] -> Strategy prim
first = foldr or stuck

any :: [Strategy prim] -> Strategy prim
any = first

-- | Attempt the given strategy once.
try :: Strategy prim -> Strategy prim
try strategy = or strategy continue

-- | Apply the strategy zero or more times.
many :: Strategy prim -> Strategy prim
many strategy = many0
  where
    many0 = or (seq strategy many0) continue

-- | Apply the strategy one or more times.
some :: Strategy prim -> Strategy prim
some strategy = seq strategy (many strategy)

-- | Apply the rewrite rule, then advance to the next strategy.
apply ::
    -- | rule
    prim ->
    Strategy prim
apply = Apply

{- | Produce no children; the end of all strategies.

@stuck@ does not necessarily indicate unsuccessful termination, but it
is not generally possible to determine if one branch of execution is
successful without looking at all the branches.

@stuck@ is the annihilator of 'seq':
@
seq stuck a === stuck
seq a stuck === stuck
@

@stuck@ is the identity of 'and':
@
and stuck a === a
and a stuck === a
@

@stuck@ is the left-identity of 'or':
@
or stuck a === a
@
-}
stuck :: Strategy prim
stuck = Stuck

{- | Produce one child identical to its parent.

@continue@ is the identity of 'seq':
@
seq continue a === a
seq a continue === a
@
-}
continue :: Strategy prim
continue = Continue

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
    , -- | The predecessor configurations in the execution graph and the sequence
      -- of rules applied from the parent configuration to the present
      -- configuration.
      parents :: [(Seq rule, Graph.Node)]
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
    Strategy prim ->
    -- | execution graph so far
    ExecutionGraph config rule ->
    -- | current "selected" node
    Graph.Node ->
    -- | graph with one more step executed for the selected node
    m (ExecutionGraph config rule)
executionHistoryStep transit prim exe@ExecutionGraph{graph} node
    | nodeIsNotLeaf = error "Node has already been evaluated"
    | otherwise =
        case Graph.lab graph node of
            Nothing -> error "Node does not exist"
            Just config -> do
                configs <- runTransitionT (transitionRule transit prim config)
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
        -- | Child node identifier and configuration
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

@leavesM@ returns a disjunction of leaves (vertices without descendants) rather
than constructing the entire graph.

The queue updating function should be 'unfoldBreadthFirst' or
'unfoldDepthFirst', optionally composed with 'applyBreadthLimit'.
-}
leavesM ::
    forall m a.
    Monad m =>
    Alternative m =>
    -- | queue updating function
    ([a] -> Seq a -> m (Seq a)) ->
    -- | unfolding function
    (a -> m [a]) ->
    -- | initial vertex
    a ->
    m a
leavesM mkQueue next a0 =
    mkQueue [a0] Seq.empty >>= worker
  where
    worker Seq.Empty = empty
    worker (a Seq.:<| as) =
        do
            as' <- lift (next a)
            (guard . not) (null as')
            lift (mkQueue as' as)
            & maybeT (return a <|> worker as) worker

{- | Unfold the function from the initial vertex.

@unfoldM_@ visits every descendant in the graph, but unlike 'leavesM' does not
return any values.

The queue updating function should be 'unfoldBreadthFirst' or
'unfoldDepthFirst', optionally composed with 'applyBreadthLimit'.

See also: 'leavesM'
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
    Monad m =>
    -- | Primitive strategy rule
    (prim -> config -> TransitionT rule m config) ->
    (Strategy prim -> config -> TransitionT rule m config)
transitionRule applyPrim = transitionRule0
  where
    transitionRule0 =
        \case
            Seq instr1 instr2 -> transitionSeq instr1 instr2
            And instr1 instr2 -> transitionAnd instr1 instr2
            Or instr1 instr2 -> transitionOr instr1 instr2
            Apply prim -> transitionApply prim
            Continue -> transitionContinue
            Stuck -> transitionStuck

    -- End execution.
    transitionStuck _ = empty

    transitionContinue result = return result

    -- Apply the instructions in sequence.
    transitionSeq instr1 instr2 =
        transitionRule0 instr1 >=> transitionRule0 instr2

    -- Attempt both instructions, i.e. create a branch for each.
    transitionAnd instr1 instr2 config =
        transitionRule0 instr1 config <|> transitionRule0 instr2 config

    -- Attempt the first instruction. Fall back to the second if it is
    -- unsuccessful.
    transitionOr instr1 instr2 config = do
        results <- tryTransitionT (transitionRule0 instr1 config)
        case results of
            [] -> transitionRule0 instr2 config
            _ -> scatter results

    -- Apply a primitive rule. Throw an exception if the rule is not successful.
    transitionApply = applyPrim

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
    -- | Strategies
    [Strategy prim] ->
    -- | Initial configuration
    config ->
    m (ExecutionGraph config rule)
runStrategy breadthLimit applyPrim instrs0 config0 =
    runStrategyWithSearchOrder breadthLimit applyPrim instrs0 BreadthFirst config0

runStrategyWithSearchOrder ::
    forall m prim rule config.
    MonadThrow m =>
    Limit Natural ->
    -- | Primitive strategy rule
    (prim -> config -> TransitionT rule m config) ->
    -- | Strategies
    [Strategy prim] ->
    -- | Search order of the execution graph
    GraphSearchOrder ->
    -- | Initial configuration
    config ->
    m (ExecutionGraph config rule)
runStrategyWithSearchOrder breadthLimit applyPrim instrs0 searchOrder0 config0 =
    constructExecutionGraph
        breadthLimit
        (transitionRule applyPrim)
        instrs0
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
pickLongest exeGraph = head $ last $ history exeGraph

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
