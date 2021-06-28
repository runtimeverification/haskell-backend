module Test.Kore.Internal.MultiExists (
    test_refresh,
    test_filterRelevant,
    test_Semigroup,
) where

import Data.Maybe (
    fromJust,
 )
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Kore.Internal.MultiExists
import Kore.Internal.TermLike
import Kore.Variables.Fresh (
    refreshElementVariable,
 )
import Prelude.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

x, x', y :: ElementVariable VariableName
x = Mock.x
x' = refreshElementVariable (mkAvoid [x]) x & fromJust
y = Mock.y

mkAvoid :: [ElementVariable VariableName] -> Set (SomeVariableName VariableName)
mkAvoid = Set.fromList . map (inject . variableName)

test_refresh :: [TestTree]
test_refresh =
    [ testCase "refresh relevant variables" $ do
        let input = quantify x (unquantified $ mkElemVar x)
            avoid = (Set.map (inject . variableName) . Set.fromList) [x]
            actual = refresh avoid input
            expect = quantify x' (unquantified $ mkElemVar x')
        assertEqual "" expect actual
    , testCase "do not refresh irrelevant variables" $ do
        let input = quantify x (unquantified $ mkElemVar x)
            avoid = Set.empty
            actual = refresh avoid input
            expect = input
        assertEqual "" expect actual
    ]

test_filterRelevant :: [TestTree]
test_filterRelevant =
    [ testCase "keep relevant variables" $ do
        let input = quantify x (unquantified $ mkElemVar x)
            expect = input
            actual = filterRelevant input
        assertEqual "" expect actual
    , testCase "remove irrelevant variables" $ do
        let input = quantify x (quantify y (unquantified $ mkElemVar x))
            expect = quantify x (unquantified $ mkElemVar x)
            actual = filterRelevant input
        assertEqual "" expect actual
    ]

test_Semigroup :: [TestTree]
test_Semigroup =
    [ testCase "do not refresh irrelevant variables" $ do
        let input1 = quantify x (unquantified [mkElemVar x])
            input2 = quantify y (unquantified [mkElemVar y])
            actual = input1 <> input2
            expect =
                (quantify x . quantify y)
                    (unquantified [mkElemVar x, mkElemVar y])
        assertEqual "" expect actual
    , testCase "do not capture right free variables" $ do
        let input1 = quantify x (unquantified [mkElemVar x])
            input2 = unquantified [mkElemVar x]
            actual = input1 <> input2
            expect =
                quantify x' (unquantified [mkElemVar x', mkElemVar x])
        assertEqual "" expect actual
    , testCase "do not capture left free variables" $ do
        let input2 = quantify x (unquantified [mkElemVar x])
            input1 = unquantified [mkElemVar x]
            actual = input1 <> input2
            expect =
                quantify x' (unquantified [mkElemVar x, mkElemVar x'])
        assertEqual "" expect actual
    , testCase "do not confuse bound variables" $ do
        let input = quantify x (unquantified [mkElemVar x])
            actual = input <> input
            expect =
                (quantify x . quantify x')
                    (unquantified [mkElemVar x, mkElemVar x'])
        assertEqual "" expect actual
    ]
