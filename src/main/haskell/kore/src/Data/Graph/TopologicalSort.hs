{-|
Module      : Data.Graph.TopologicalSort
Description : Topological sorting algorithm.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Graph.TopologicalSort
    ( topologicalSort
    , ToplogicalSortCycles(..)
    ) where

import           Data.Graph
                 ( SCC (..), stronglyConnComp )
import qualified Data.Map as Map

newtype ToplogicalSortCycles node = ToplogicalSortCycles [node]
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
    -> Either (ToplogicalSortCycles node) [node]
topologicalSort edges =
    mapM
        extractSortedNode
        (stronglyConnComp
            (map
                (\ (node, edges') -> (node, node, edges'))
                (Map.toList edges)
            )
        )
  where
    extractSortedNode :: SCC node -> Either (ToplogicalSortCycles node) node
    extractSortedNode (AcyclicSCC n)    = Right n
    extractSortedNode (CyclicSCC nodes) = Left (ToplogicalSortCycles nodes)
