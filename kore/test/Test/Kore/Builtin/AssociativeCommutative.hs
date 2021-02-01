{-# LANGUAGE Strict #-}

module Test.Kore.Builtin.AssociativeCommutative where

import Prelude.Kore

-- import Test.Tasty

import Kore.Builtin.AssociativeCommutative
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.TermLike

-- import qualified Test.Kore.Step.MockSymbols as Mock
-- import Test.Tasty.HUnit.Ext

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
