module Test.Data.Graph.TopologicalSort
    (test_topologicalSort) where

import Test.Tasty

import qualified Data.Map as Map

import Data.Graph.TopologicalSort

import Test.Tasty.HUnit.Ext

test_topologicalSort :: [TestTree]
test_topologicalSort =
    [ testCase "Empty graph"
        (assertEqual ""
            (Right [])
            (topologicalSort
                (Map.empty :: Map.Map Integer [Integer])
            )
        )
    , testCase "One node"
        (assertEqual ""
            (Right [1])
            (topologicalSort
                (Map.fromList [(1, [])] :: Map.Map Integer [Integer])
            )
        )
    , testCase "Two ordered nodes"
        (assertEqual ""
            (Right [2, 1])
            (topologicalSort
                (Map.fromList
                    [ (1, [2])
                    , (2, [])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    , testCase "Three ordered nodes, minimal edges"
        (assertEqual ""
            (Right [3, 2, 1])
            (topologicalSort
                (Map.fromList
                    [ (1, [2])
                    , (2, [3])
                    , (3, [])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    , let
        sorted =
            topologicalSort
                (Map.fromList
                    [ (1, [2])
                    , (3, [2])
                    , (2, [])
                    ]
                :: Map.Map Integer [Integer]
                )
      in
        testCase "Three nodes, one lower than the others"
            (assertEqual "" (Right [2, 3, 1]) sorted)
    , testCase "Three nodes, total order"
        (assertEqual ""
            (Right [3, 2, 1])
            (topologicalSort
                (Map.fromList
                    [ (1, [2, 3])
                    , (2, [3])
                    , (3, [])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    , testCase "Four nodes, diamond"
        (assertEqual ""
            (Right [4, 3, 2, 1])
            (topologicalSort
                (Map.fromList
                    [ (1, [3, 2])
                    , (2, [4])
                    , (3, [4])
                    , (4, [])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    , testCase "Simple cycle"
        (assertEqual ""
            (Left (TopologicalSortCycles [1]))
            (topologicalSort
                (Map.fromList
                    [ (1, [1])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    , testCase "Long cycle"
        (assertEqual ""
            (Left (TopologicalSortCycles [1, 2, 3]))
            (topologicalSort
                (Map.fromList
                    [ (1, [2])
                    , (2, [3])
                    , (3, [1])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    , testCase "Cycle not starting at the first visited node"
        (assertEqual ""
            (Left (TopologicalSortCycles [2, 3]))
            (topologicalSort
                (Map.fromList
                    [ (1, [2])
                    , (2, [3])
                    , (3, [2])
                    ]
                :: Map.Map Integer [Integer]
                )
            )
        )
    ]
