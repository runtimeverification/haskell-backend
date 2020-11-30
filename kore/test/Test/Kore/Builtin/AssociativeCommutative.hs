module Test.Kore.Builtin.AssociativeCommutative
    ( test_toNormalized_Map
    , test_matchBuiltin_Map
    , test_toNormalized_Set
    , test_matchBuiltin_Set
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Builtin.AssociativeCommutative
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.TermLike

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_toNormalized_Map :: [TestTree]
test_toNormalized_Map =
    [ testCase "removes Defined" $ do
        let elements =
                -- Need two elements to ensure that Defined wrapper is kept.
                [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.y, Mock.b)]
            expect = mkNormalizedMap elements
            actual = toNormalized $ mkDefined $ Mock.builtinMap elements
        assertEqual "" expect actual
    ]

test_matchBuiltin_Map :: [TestTree]
test_matchBuiltin_Map =
    [ testCase "removes Defined" $ do
        let input :: TermLike VariableName
            input = mkDefinedAtTop $ Mock.builtinMap [(Mock.a, Mock.a)]
            actual = matchBuiltin @NormalizedMap input
        assertBool "expected to match Defined builtin Map" (isJust actual)
    ]

test_toNormalized_Set :: [TestTree]
test_toNormalized_Set =
    [ testCase "removes Defined" $ do
        let elements =
                -- Need two elements to ensure that Defined wrapper is kept.
                [mkElemVar Mock.x, mkElemVar Mock.y]
            expect = mkNormalizedSet elements
            actual = toNormalized $ mkDefined $ Mock.builtinSet elements
        assertEqual "" expect actual
    ]

test_matchBuiltin_Set :: [TestTree]
test_matchBuiltin_Set =
    [ testCase "removes Defined" $ do
        let input :: TermLike VariableName
            input = mkDefinedAtTop $ Mock.builtinSet [Mock.a]
            actual = matchBuiltin @NormalizedSet input
        assertBool "expected to match Defined builtin Set" (isJust actual)
    ]

mkNormalizedMap
    :: [(TermLike VariableName, TermLike VariableName)]
    -> NormalizedOrBottom NormalizedMap VariableName
mkNormalizedMap =
    Normalized . NormalizedMap . mkNormalizedAC . (fmap . fmap) MapValue

mkNormalizedSet
    :: [TermLike VariableName]
    -> NormalizedOrBottom NormalizedSet VariableName
mkNormalizedSet =
    Normalized . NormalizedSet . mkNormalizedAC . fmap (\x -> (x, SetValue))

mkNormalizedAC
    :: AcWrapper collection
    => [(child, Value collection child)]
    -> NormalizedAc collection key child
mkNormalizedAC elements =
    emptyNormalizedAc
        { elementsWithVariables =
            fmap wrapElement elements
        }
