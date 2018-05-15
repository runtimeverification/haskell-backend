{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Algorithm.TopologicalSort
    (topologicalSort)
  where

import qualified Data.Map                    as Map
import qualified Data.Set                    as Set

import           Data.Kore.Error
import           Data.Kore.HaskellExtensions

topologicalSort
    :: Ord node
    => Map.Map node [node]
    -> (node -> String)
    -> Either (Error e) [node]
topologicalSort edges nodePrinter =
    reversedToList . fst <$>
        topologicalSortReversed
            nodePrinter (Map.keys edges) edges Set.empty emptyReversedList
{-
    Data.Graph would be nice in theory but its topsort does not fail for
    unsortable graphs.

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
    :: Ord node
    => (node -> String)
    -> [node]
    -> Map.Map node [node]
    -> Set.Set node
    -> ReversedList node
    -> Either (Error e) (ReversedList node, Set.Set node)
topologicalSortReversed _ [] _ usedNodes reversedOrder =
    return (reversedOrder, usedNodes)
topologicalSortReversed nodePrinter (node:nodes) edges usedNodes reversedOrder
  | Set.member node usedNodes
  = topologicalSortReversed nodePrinter nodes edges usedNodes reversedOrder
topologicalSortReversed nodePrinter (node:nodes) edges usedNodes reversedOrder
  = do
    (subtreeUsedNodes, subtreeReversedOrder) <-
        topologicalSortTraverse
            nodePrinter node edges Set.empty (usedNodes, reversedOrder)
    topologicalSortReversed
        nodePrinter
        nodes
        edges
        subtreeUsedNodes
        subtreeReversedOrder

topologicalSortTraverse
    :: Ord node
    => (node -> String)
    -> node
    -> Map.Map node [node]
    -> Set.Set node
    -> (Set.Set node, ReversedList node)
    -> Either (Error e) (Set.Set node, ReversedList node)
topologicalSortTraverse
    _ node _ _ (usedNodes, reversedOrder)
  | Set.member node usedNodes
  = return (usedNodes, reversedOrder)
topologicalSortTraverse
    nodePrinter node edges nodesStack (usedNodes, reversedOrder)
  = do
    koreFailWhen
        (Set.member node nodesStack)
        (  "Graph cycle starting at "
        ++ nodePrinter node
        ++ " and containing "
        ++ show (map nodePrinter (Set.toList nodesStack))
        ++ "."
        )
    case Map.lookup node edges of
        Just (n:ns) -> do
            (newUsedNodes, newReversedOrder) <-
                traverseSubnodes
                    nodePrinter
                    (n:ns)
                    edges
                    (Set.insert node nodesStack)
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
                ++ nodePrinter node
                ++ " does not have an edge list."
                )

traverseSubnodes
    :: Ord node
    => (node -> String)
    -> [node]
    -> Map.Map node [node]
    -> Set.Set node
    -> (Set.Set node, ReversedList node)
    -> Either (Error e) (Set.Set node, ReversedList node)
traverseSubnodes _ [] _ _ (usedNodes, reversedOrder) =
    return (usedNodes, reversedOrder)
traverseSubnodes nodePrinter (n:ns) edges nodesStack (usedNodes, reversedOrder)
  = do
    (newUsedNodes, newReversedOrder) <-
        topologicalSortTraverse
            nodePrinter n edges nodesStack (usedNodes, reversedOrder)
    traverseSubnodes
        nodePrinter ns edges nodesStack (newUsedNodes, newReversedOrder)
