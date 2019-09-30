{-|
Module      : Data.Graph.TopologicalSort
Description : Topological sorting algorithm.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Graph.TopologicalSort
    ( topologicalSort
    , TopologicalSortCycles(..)
    ) where

import Data.Graph
    ( SCC (..)
    , stronglyConnComp
    )
import qualified Data.Map as Map
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug

newtype TopologicalSortCycles node = TopologicalSortCycles [node]
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic (TopologicalSortCycles node)

instance SOP.HasDatatypeInfo (TopologicalSortCycles node)

instance Debug node => Debug (TopologicalSortCycles node)

instance (Debug node, Diff node) => Diff (TopologicalSortCycles node)

{-| 'topologicalSort' sorts a graph topologically, starting with nodes which
have no 'next' nodes.
The graph is provided as a map form nodes to the list of their adjacent 'next'
nodes. All nodes must be present as keys in the map, even if they have no 'next'
nodes.
Returns an error for graphs that have cycles.
-}
topologicalSort
    :: (Ord node, Show node)
    => Map.Map node [node]
    -> Either (TopologicalSortCycles node) [node]
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
    extractSortedNode :: SCC node -> Either (TopologicalSortCycles node) node
    extractSortedNode (AcyclicSCC n)    = Right n
    extractSortedNode (CyclicSCC nodes) = Left (TopologicalSortCycles nodes)
