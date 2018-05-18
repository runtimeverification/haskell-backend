{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Data.Kore.Algorithm.TopologicalSort
Description : Topological sorting algorithm.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Algorithm.TopologicalSort
    (topologicalSort, ToplogicalSortCycle(..))
  where

import           Control.Monad                             (when)
import qualified Data.Map                                  as Map
import qualified Data.Set                                  as Set

import qualified Data.Kore.Algorithm.SetWithInsertionOrder as Swio
import           Data.Kore.HaskellExtensions

newtype ToplogicalSortCycle node = ToplogicalSortCycle [node]
    deriving (Show, Eq)

{--| 'topologicalSort' sorts a graph topologically, starting with nodes which
have no 'next' nodes.
The graph is provided as a map form nodes to the list of their adjacent 'next'
nodes. All nodes must be present as keys in the map, even if they have no 'next'
nodes.
Returns an error for graphs that have cycles.
--}
topologicalSort
    :: (Ord node, Show node)
    => Map.Map node [node]
    -> Either (ToplogicalSortCycle node) [node]
topologicalSort edges =
    reversedToList . fst <$>
        topologicalSortReversed
            (Map.keys edges) edges Set.empty emptyReversedList
{-
    Data.Graph would be nice in theory (see the reminder of this comment),
    but its topSort function does not fail for unsortable graphs.
topologicalSort edges =
    map indexNode (Graph.topSort graph)
  where
    nodeToVertex [] = (Map.empty, Map.empty)
    nodeToVertex (node : nodes) =
        ( Map.insert node mapSize nodeToIndex'
        , Map.insert mapSize node indexToNode'
        )
      where
        (nodeToIndex', indexToNode') = nodeToVertex nodes
        mapSize = Map.size nodeToIndex
    (nodeToIndex, indexToNode) = nodeToVertex (Map.keys edges)
    graph :: Graph.Graph
    graph = Array.array (0, Map.size nodeToIndex) intEdges
    intEdges :: [(Int, [Int])]
    intEdges =
        map
            (\(node, nodes) -> (nodeIndex node, map nodeIndex nodes))
            (Map.toList edges)
    nodeIndex node =
        fromMaybe
            (error "Internal error: cannot find node in index.")
            (Map.lookup node nodeToIndex)
    indexNode index =
        fromMaybe
            (error "Internal error: cannot find node for index.")
            (Map.lookup index indexToNode)
-}

topologicalSortReversed
    :: (Ord node, Show node)
    => [node]
    -> Map.Map node [node]
    -> Set.Set node
    -> ReversedList node
    -> Either (ToplogicalSortCycle node) (ReversedList node, Set.Set node)
topologicalSortReversed [] _ usedNodes reversedOrder =
    return (reversedOrder, usedNodes)
topologicalSortReversed (node:nodes) edges usedNodes reversedOrder
  | Set.member node usedNodes
  = topologicalSortReversed nodes edges usedNodes reversedOrder
topologicalSortReversed (node:nodes) edges usedNodes reversedOrder
  = do
    (subtreeUsedNodes, subtreeReversedOrder) <-
        topologicalSortTraverse
            node edges Swio.empty (usedNodes, reversedOrder)
    topologicalSortReversed
        nodes
        edges
        subtreeUsedNodes
        subtreeReversedOrder

topologicalSortTraverse
    :: (Show node, Ord node)
    => node
    -> Map.Map node [node]
    -> Swio.SetWithInsertionOrder node
    -> (Set.Set node, ReversedList node)
    -> Either (ToplogicalSortCycle node) (Set.Set node, ReversedList node)
topologicalSortTraverse
    node _ _ (usedNodes, reversedOrder)
  | Set.member node usedNodes
  = return (usedNodes, reversedOrder)
topologicalSortTraverse
    node edges nodesStack (usedNodes, reversedOrder)
  = do
    when
        (Swio.member node nodesStack)
        (Left
            (toplogicalSortCycle
                node
                (Swio.insertionOrder nodesStack ++ [node])
            )
        )
    case Map.lookup node edges of
        Just (n:ns) -> do
            (newUsedNodes, newReversedOrder) <-
                traverseSubnodes
                    (n:ns)
                    edges
                    (Swio.insert node nodesStack)
                    (usedNodes, reversedOrder)
            return
                ( Set.insert node newUsedNodes
                , node `reversedAdd` newReversedOrder
                )
        Just [] ->
            return
                ( Set.insert node usedNodes
                , node `reversedAdd` reversedOrder
                )
        Nothing ->
            error
                (  "Internal error: "
                ++ show node
                ++ " does not have an edge list."
                )
  where
    toplogicalSortCycle
        :: Eq node => node -> [node] -> ToplogicalSortCycle node
    toplogicalSortCycle _ [] = error "Empty cycle"
    toplogicalSortCycle _ [_] = error "Length 1 cycle"
    toplogicalSortCycle start (n:ns)
        | start == n = ToplogicalSortCycle (n:ns)
        | otherwise = toplogicalSortCycle start ns

traverseSubnodes
    :: (Show node, Ord node)
    => [node]
    -> Map.Map node [node]
    -> Swio.SetWithInsertionOrder node
    -> (Set.Set node, ReversedList node)
    -> Either (ToplogicalSortCycle node) (Set.Set node, ReversedList node)
traverseSubnodes [] _ _ (usedNodes, reversedOrder) =
    return (usedNodes, reversedOrder)
traverseSubnodes (n:ns) edges nodesStack (usedNodes, reversedOrder)
  = do
    (newUsedNodes, newReversedOrder) <-
        topologicalSortTraverse
            n edges nodesStack (usedNodes, reversedOrder)
    traverseSubnodes
        ns edges nodesStack (newUsedNodes, newReversedOrder)
