module Test.Kore.Internal.MultiAnd (
    test_multiAndTopBottom,
    test_make,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import Kore.Internal.From
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Predicate (Predicate)
import Kore.Internal.TermLike (ElementVariable, mkElemVar)
import Kore.Rewriting.RewritingVariable (RewritingVariableName)
import Kore.TopBottom (
    TopBottom (..),
 )
import Prelude.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

data TestTopBottom = TestTop | TestBottom | TestOther !Integer
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance TopBottom TestTopBottom where
    isTop TestTop = True
    isTop _ = False
    isBottom TestBottom = True
    isBottom _ = False

test_multiAndTopBottom :: [TestTree]
test_multiAndTopBottom =
    [ assertIsTop True (MultiAnd.make [])
    , assertIsTop True (MultiAnd.make [TestTop])
    , assertIsTop False (MultiAnd.make [TestTop, TestOther 1])
    , assertIsTop False (MultiAnd.make [TestTop, TestBottom])
    , assertIsTop False (MultiAnd.make [TestOther 1])
    , assertIsTop False (MultiAnd.make [TestBottom])
    , assertIsBottom False (MultiAnd.make [])
    , assertIsBottom False (MultiAnd.make [TestTop])
    , assertIsBottom False (MultiAnd.make [TestTop, TestOther 1])
    , assertIsBottom True (MultiAnd.make [TestTop, TestBottom])
    , assertIsBottom False (MultiAnd.make [TestOther 1])
    , assertIsBottom True (MultiAnd.make [TestBottom])
    ]

test_make :: [TestTree]
test_make =
    [ MultiAnd.make [] `hasPatterns` []
    , MultiAnd.make [TestTop] `hasPatterns` []
    , MultiAnd.make [TestTop, TestOther 1] `hasPatterns` [TestOther 1]
    , MultiAnd.make [TestTop, TestBottom] `hasPatterns` [TestBottom]
    , MultiAnd.make [TestOther 1, TestOther 1] `hasPatterns` [TestOther 1]
    , MultiAnd.make [TestBottom] `hasPatterns` [TestBottom]
    , MultiAnd.make [TestOther 1, TestOther 2]
        `hasPatterns` [TestOther 1, TestOther 2]
    , testCase "single \\equals" $ do
        let input = [fromEquals_ (mkElemVar x) (mkElemVar y)]
            expect = input
            actual :: MultiAnd (Predicate RewritingVariableName)
            actual = MultiAnd.make input
        assertEqual "" expect (toList actual)
    ]
  where
    x, y :: ElementVariable RewritingVariableName
    x = Mock.xConfig
    y = Mock.yConfig

hasPatterns :: MultiAnd TestTopBottom -> [TestTopBottom] -> TestTree
hasPatterns actual expected =
    testCase
        "hasPattern"
        (assertEqual "" expected (toList actual))

assertIsTop :: Bool -> MultiAnd TestTopBottom -> TestTree
assertIsTop expected input =
    testCase
        "isTop"
        ( assertEqual
            ""
            expected
            (isTop input)
        )

assertIsBottom :: Bool -> MultiAnd TestTopBottom -> TestTree
assertIsBottom expected input =
    testCase
        "isBottom"
        ( assertEqual
            ""
            expected
            (isBottom input)
        )
