module Test.Kore.Internal.MultiAnd where

import Test.Tasty

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.TopBottom
    ( TopBottom (..)
    )

import Test.Tasty.HUnit.Ext

data TestTopBottom = TestTop | TestBottom | TestOther !Integer
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic TestTopBottom

instance SOP.HasDatatypeInfo TestTopBottom

instance Debug TestTopBottom

instance Diff TestTopBottom

instance TopBottom TestTopBottom where
    isTop TestTop = True
    isTop _ = False
    isBottom TestBottom = True
    isBottom _ = False

test_multiAndTopBottom :: [TestTree]
test_multiAndTopBottom =
    [ assertIsTop True  (MultiAnd.make [])
    , assertIsTop True  (MultiAnd.make [TestTop])
    , assertIsTop False (MultiAnd.make [TestTop, TestOther 1])
    , assertIsTop False (MultiAnd.make [TestTop, TestBottom])
    , assertIsTop False (MultiAnd.make [TestOther 1])
    , assertIsTop False (MultiAnd.make [TestBottom])

    , assertIsBottom False (MultiAnd.make [])
    , assertIsBottom False (MultiAnd.make [TestTop])
    , assertIsBottom False (MultiAnd.make [TestTop, TestOther 1])
    , assertIsBottom True  (MultiAnd.make [TestTop, TestBottom])
    , assertIsBottom False (MultiAnd.make [TestOther 1])
    , assertIsBottom True  (MultiAnd.make [TestBottom])
    ]

test_multiAndMake :: [TestTree]
test_multiAndMake =
    [ MultiAnd.make []                         `hasPatterns` []
    , MultiAnd.make [TestTop]                  `hasPatterns` []
    , MultiAnd.make [TestTop, TestOther 1]     `hasPatterns` [TestOther 1]
    , MultiAnd.make [TestTop, TestBottom]      `hasPatterns` [TestBottom]
    , MultiAnd.make [TestOther 1, TestOther 1] `hasPatterns` [TestOther 1]
    , MultiAnd.make [TestBottom]               `hasPatterns` [TestBottom]
    , MultiAnd.make [TestOther 1, TestOther 2]
        `hasPatterns` [TestOther 1, TestOther 2]
    ]

hasPatterns :: MultiAnd TestTopBottom -> [TestTopBottom] -> TestTree
hasPatterns actual expected =
    testCase "hasPattern"
        (assertEqual ""
            expected
            (MultiAnd.extractPatterns actual)
        )

assertIsTop :: Bool -> MultiAnd TestTopBottom -> TestTree
assertIsTop expected input =
    testCase "isTop"
        (assertEqual ""
            expected
            (isTop input)
        )

assertIsBottom :: Bool -> MultiAnd TestTopBottom -> TestTree
assertIsBottom expected input =
    testCase "isBottom"
        (assertEqual ""
            expected
            (isBottom input)
        )
