module Test.Kore.Builtin.AssociativeCommutative
    ( test_toNormalized_Map
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Builtin.AssociativeCommutative
import Kore.Domain.Builtin
    ( NormalizedAc (..)
    , NormalizedMap (..)
    , Value (..)
    , emptyNormalizedAc
    , wrapElement
    )
import Kore.Internal.TermLike

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

test_toNormalized_Map :: [TestTree]
test_toNormalized_Map =
    [ testCase "removes Defined" $ do
        let elements =
                -- Need two elements to ensure that Defined wrapper is kept.
                [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.y, Mock.b)]
            normalizedMap =
                NormalizedMap emptyNormalizedAc
                { elementsWithVariables =
                    map (\(x, y) -> wrapElement (x, MapValue y)) elements
                }
            expect = Normalized normalizedMap
            actual = toNormalized $ mkDefined $ Mock.builtinMap elements
        assertEqual "" expect actual
    ]
