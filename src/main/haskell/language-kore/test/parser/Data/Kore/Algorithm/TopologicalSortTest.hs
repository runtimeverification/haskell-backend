module Data.Kore.Algorithm.TopologicalSortTest
    (topologicalSortTest) where

import           Test.Tasty                          (TestTree, testGroup)
import           Test.Tasty.HUnit                    (assertEqual, testCase)

import qualified Data.Map                            as Map

import           Data.Kore.Algorithm.TopologicalSort
import           Data.Kore.Error

topologicalSortTest :: TestTree
topologicalSortTest =
    testGroup
        "Topological sort test"
        [ testCase "Empty graph"
            (assertEqual ""
                (Right [])
                (topologicalSort
                    (Map.empty :: Map.Map Integer [Integer])
                    show
                )
            )
        , testCase "One node"
            (assertEqual ""
                (Right [1])
                (topologicalSort
                    (Map.fromList [(1, [])] :: Map.Map Integer [Integer])
                    show
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
                    show
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
                    show
                )
            )
        , testCase "Three nodes, one lower than the others"
            (assertEqual ""
                (Right [2, 1, 3])
                (topologicalSort
                    (Map.fromList
                        [ (1, [2])
                        , (3, [2])
                        , (2, [])
                        ]
                    :: Map.Map Integer [Integer]
                    )
                    show
                )
            )
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
                    show
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
                    show
                )
            )
        , testCase "Simple cycle"
            (assertEqual ""
                (Left
                    (Error
                        []
                        "Graph cycle starting at 1 and containing [\"1\"]."
                    )
                )
                (topologicalSort
                    (Map.fromList
                        [ (1, [1])
                        ]
                    :: Map.Map Integer [Integer]
                    )
                    show
                )
            )
        , testCase "Long cycle"
            (assertEqual ""
                (Left
                    (Error
                        []
                        (  "Graph cycle starting at 1 and containing "
                        ++ "[\"1\",\"2\",\"3\"]."
                        )
                    )
                )
                (topologicalSort
                    (Map.fromList
                        [ (1, [2])
                        , (2, [3])
                        , (3, [1])
                        ]
                    :: Map.Map Integer [Integer]
                    )
                    show
                )
            )
        ]
