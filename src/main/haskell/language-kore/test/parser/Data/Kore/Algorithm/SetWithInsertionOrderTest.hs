module Data.Kore.Algorithm.SetWithInsertionOrderTest
    (setWithInsertionOrderTest) where

import           Test.Tasty                                (TestTree, testGroup)
import           Test.Tasty.HUnit                          (assertEqual,
                                                            testCase)

import           Data.Kore.Algorithm.SetWithInsertionOrder

setWithInsertionOrderTest :: TestTree
setWithInsertionOrderTest =
    testGroup
        "Set with insertion order test"
        [ testCase "Empty set - list"
            (assertEqual ""
                []
                (insertionOrder intEmpty)
            )
        , testCase "One element set - list"
            (assertEqual ""
                [10]
                (insertionOrder $ insert 10 intEmpty)
            )
        , testCase "Multiple element set - list"
            (assertEqual ""
                [13, 8, 10]
                (insertionOrder $ insert 10 $ insert 8 $ insert 13 intEmpty)
            )
        , let mySet = insert 10 $ insert 8 $ insert 13 intEmpty
          in testCase "Multiple element set - element in set"
            (do
                assertEqual "" True (member 10 mySet)
                assertEqual "" True (member 13 mySet)
                assertEqual "" False (member 11 mySet)
            )
        ]
  where
    intEmpty :: SetWithInsertionOrder Int
    intEmpty = empty
