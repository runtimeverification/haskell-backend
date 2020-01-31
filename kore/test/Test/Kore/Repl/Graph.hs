module Test.Kore.Repl.Graph
    ( test_graph
    ) where

import Test.Tasty
import Test.Tasty.HUnit.Ext

import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree
    ( Gr
    )
import Data.Set
    ( Set
    , isSubsetOf
    )
import qualified Data.Set as Set

import Kore.Repl.Interpreter
    ( smoothOutGraph
    )

-- TODO: test actual == expected
test_graph :: [TestTree]
test_graph =
    [ testGroup "Smooth out graph with a single node"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet g1' `isSubsetOf` nodesSet g1)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size g1' <= Graph.size g1)
        , testCase "The only nodes with in/out degree == 1\
                    \ are included in the children of branchings" $
            assertBool ""
                $ Set.fromList (inOutDegreeOne g1')
                `isSubsetOf` Set.fromList (childrenOfBranchings g1)
        ]
    , testGroup "Smooth out chain graph"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet chain' `isSubsetOf` nodesSet chain)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size chain' <= Graph.size chain)
        , testCase "The only nodes with in/out degree == 1\
                    \ are included in the children of branchings" $
            assertBool ""
                $ Set.fromList (inOutDegreeOne chain')
                `isSubsetOf` Set.fromList (childrenOfBranchings chain)
        ]
    , testGroup "Smooth out arbitrary tree1"
        [ testCase "Contains only a subset of the original nodes" $ do
            assertBool "" (nodesSet tree1' `isSubsetOf` nodesSet tree1)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size tree1' <= Graph.size tree1)
        , testCase "The only nodes with in/out degree == 1\
                    \ are included in the children of branchings" $ do
            assertBool ""
                $ Set.fromList (inOutDegreeOne tree1')
                `isSubsetOf` Set.fromList (childrenOfBranchings tree1)
        ]
    , testGroup "TESTING Smooth out tree with branching at the root"
        [ testCase "Contains only a subset of the original nodes" $ do
            assertBool "" (nodesSet tree2' `isSubsetOf` nodesSet tree2)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size tree2' <= Graph.size tree2)
        , testCase "The only nodes with in/out degree == 1\
                    \ are included in the children of branchings" $ do
            assertBool ""
                $ Set.fromList (inOutDegreeOne tree2')
                `isSubsetOf` Set.fromList (childrenOfBranchings tree2)
        ]
    ]

inOutDegreeOne :: Gr a b -> [Graph.Node]
inOutDegreeOne gr =
    Graph.nodes
        ( Graph.nfilter
            (\n -> (Graph.indeg gr n == 1) && (Graph.outdeg gr n == 1))
            gr
        )

childrenOfBranchings :: Gr a b -> [Graph.Node]
childrenOfBranchings gr =
    Graph.nodes
        ( Graph.nfilter
            (\n -> Graph.outdeg gr n > 1)
            gr
        )
    >>= Graph.suc gr

nodesSet :: Gr a b -> Set Graph.Node
nodesSet = Set.fromList . Graph.nodes

g1, chain, tree1, tree2 :: Gr () ()
g1 = Graph.mkUGraph [1] []
chain = Graph.mkUGraph [0..100] [(x, y) | x <- [0..99], let y = x + 1]
tree1 =
    Graph.mkUGraph
        [0..13]
        [ (0, 1), (1, 2), (1, 3), (2, 4)
        , (4, 5), (5, 6), (5, 7), (5, 8)
        , (6, 9), (8, 10), (3, 11), (11, 12)
        , (12, 13)
        ]
tree2 =
    Graph.mkUGraph
        [0..11]
        [ (0, 1), (0, 2), (0, 3), (0, 4)
        , (2, 5), (5, 6), (6, 8), (8, 10)
        , (3, 7), (7, 9)
        , (4, 11)
        ]

g1', chain', tree1', tree2' :: Gr () (Maybe ())
g1' = smoothOutGraph g1
chain' = smoothOutGraph chain
tree1' = smoothOutGraph tree1
tree2' = smoothOutGraph tree2
