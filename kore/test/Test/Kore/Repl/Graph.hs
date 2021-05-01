{-# LANGUAGE Strict #-}

module Test.Kore.Repl.Graph (
    test_graph,
) where

import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree (
    Gr,
 )
import Data.Maybe (
    fromJust,
 )
import Data.Set (
    Set,
    isSubsetOf,
 )
import qualified Data.Set as Set
import Kore.Repl.State (
    smoothOutGraph,
 )
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit.Ext hiding (
    assert,
 )

test_graph :: [TestTree]
test_graph =
    [ testGroup
        "Smooth out graph with a single node"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet g1' `isSubsetOf` nodesSet g1)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size g1' <= Graph.size g1)
        , testCase
            "The only nodes with in/out degree == 1\
            \ are included in the children of branchings"
            $ assertBool "" $
                Set.fromList (inOutDegreeOne g1')
                    `isSubsetOf` Set.fromList (childrenOfBranchings g1)
        , testCase "actual === expected" $
            assert (g1' == expectedG1') $ return ()
        ]
    , testGroup
        "Smooth out graph with two nodes"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet g2' `isSubsetOf` nodesSet g2)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size g2' <= Graph.size g2)
        , testCase
            "The only nodes with in/out degree == 1\
            \ are included in the children of branchings"
            $ assertBool "" $
                Set.fromList (inOutDegreeOne g2')
                    `isSubsetOf` Set.fromList (childrenOfBranchings g2)
        , testCase "actual === expected" $
            assert (g2' == expectedG2') $ return ()
        ]
    , testGroup
        "Smooth out chain graph"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet chain' `isSubsetOf` nodesSet chain)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size chain' <= Graph.size chain)
        , testCase
            "The only nodes with in/out degree == 1\
            \ are included in the children of branchings"
            $ assertBool "" $
                Set.fromList (inOutDegreeOne chain')
                    `isSubsetOf` Set.fromList (childrenOfBranchings chain)
        , testCase "actual === expected" $
            assert (chain' == expectedChain') $ return ()
        ]
    , testGroup
        "Smooth out arbitrary tree1"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet tree1' `isSubsetOf` nodesSet tree1)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size tree1' <= Graph.size tree1)
        , testCase
            "The only nodes with in/out degree == 1\
            \ are included in the children of branchings"
            $ assertBool "" $
                Set.fromList (inOutDegreeOne tree1')
                    `isSubsetOf` Set.fromList (childrenOfBranchings tree1)
        , testCase "actual === expected" $
            assert (tree1' == expectedTree1') $ return ()
        ]
    , testGroup
        "Smooth out tree with branching at the root"
        [ testCase "Contains only a subset of the original nodes" $
            assertBool "" (nodesSet tree2' `isSubsetOf` nodesSet tree2)
        , testCase "Number of edges is smaller or equal" $
            assertBool "" (Graph.size tree2' <= Graph.size tree2)
        , testCase
            "The only nodes with in/out degree == 1\
            \ are included in the children of branchings"
            $ assertBool "" $
                Set.fromList (inOutDegreeOne tree2')
                    `isSubsetOf` Set.fromList (childrenOfBranchings tree2)
        , testCase "actual === expected" $
            assert (tree2' == expectedTree2') $ return ()
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

g1, g2, chain, tree1, tree2 :: Gr () ()
g1 = Graph.mkUGraph [1] []
g2 = Graph.mkUGraph [1, 2] [(1, 2)]
chain = Graph.mkUGraph [0 .. 100] [(x, y) | x <- [0 .. 99], let y = x + 1]
tree1 =
    Graph.mkUGraph
        [0 .. 13]
        [ (0, 1)
        , (1, 2)
        , (1, 3)
        , (2, 4)
        , (4, 5)
        , (5, 6)
        , (5, 7)
        , (5, 8)
        , (6, 9)
        , (8, 10)
        , (3, 11)
        , (11, 12)
        , (12, 13)
        ]
tree2 =
    Graph.mkUGraph
        [0 .. 11]
        [ (0, 1)
        , (0, 2)
        , (0, 3)
        , (0, 4)
        , (2, 5)
        , (5, 6)
        , (6, 8)
        , (8, 10)
        , (3, 7)
        , (7, 9)
        , (4, 11)
        ]

g1', g2', chain', tree1', tree2' :: Gr () (Maybe ())
g1' = fromJust $ smoothOutGraph g1
g2' = fromJust $ smoothOutGraph g2
chain' = fromJust $ smoothOutGraph chain
tree1' = fromJust $ smoothOutGraph tree1
tree2' = fromJust $ smoothOutGraph tree2

expectedG1'
    , expectedG2'
    , expectedChain'
    , expectedTree1'
    , expectedTree2' ::
        Gr () (Maybe ())
expectedG1' = Graph.mkGraph [(1, ())] []
expectedG2' =
    Graph.mkGraph
        [(1, ()), (2, ())]
        [(1, 2, Just ())]
expectedChain' =
    Graph.mkGraph
        [(0, ()), (100, ())]
        [(0, 100, Nothing)]
expectedTree1' =
    Graph.mkGraph
        [ (0, ())
        , (1, ())
        , (2, ())
        , (3, ())
        , (5, ())
        , (6, ())
        , (9, ())
        , (7, ())
        , (8, ())
        , (10, ())
        , (13, ())
        ]
        [ (0, 1, Just ())
        , (1, 2, Just ())
        , (1, 3, Just ())
        , (2, 5, Nothing)
        , (5, 6, Just ())
        , (5, 7, Just ())
        , (5, 8, Just ())
        , (6, 9, Just ())
        , (8, 10, Just ())
        , (3, 13, Nothing)
        ]
expectedTree2' =
    Graph.mkGraph
        [ (0, ())
        , (1, ())
        , (2, ())
        , (3, ())
        , (4, ())
        , (11, ())
        , (10, ())
        , (9, ())
        ]
        [ (0, 1, Just ())
        , (0, 2, Just ())
        , (0, 3, Just ())
        , (0, 4, Just ())
        , (2, 10, Nothing)
        , (3, 9, Nothing)
        , (4, 11, Just ())
        ]
