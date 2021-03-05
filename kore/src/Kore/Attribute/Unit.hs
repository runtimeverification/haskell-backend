{-|
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}

{-# LANGUAGE Strict #-}

module Kore.Attribute.Unit
    ( Unit (..)
    , mergeUnit, toUnit, fromUnit
    , unitId, unitSymbol, unitAttribute
    ) where

import Prelude.Kore

import Data.Default
import qualified Generics.SOP as SOP

import Kore.Attribute.Parser
import Kore.Debug
import Kore.Unparser

-- | @Unit@ represents the @unit@ attribute.
newtype Unit symbol = Unit { getUnit :: Maybe symbol }
    deriving (Generic, Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mergeUnit
    :: (Eq symbol , Unparse symbol)
    => Unit symbol
    -> Unit symbol
    -> Unit symbol
mergeUnit (Unit Nothing) b = b
mergeUnit a (Unit Nothing) = a
mergeUnit a@(Unit (Just aSymbol)) (Unit (Just bSymbol))
      | aSymbol == bSymbol = a
      | otherwise = error $
        "Unit symbol mismatch error! Found both "
        ++ unparseToString aSymbol
        ++ " and "
        ++ unparseToString bSymbol
        ++ " inside term. This is a bug."

instance Default (Unit symbol) where
    def = Unit { getUnit = Nothing }

instance NFData symbol => NFData (Unit symbol)

instance ParseAttributes (Unit SymbolOrAlias) where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Unit { getUnit }
          | Just _ <- getUnit = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Unit { getUnit = Just symbol }
        withApplication' = withApplication unitId
        failDuplicate' = failDuplicate unitId

instance From (Unit SymbolOrAlias) Attributes where
    from =
        maybe def toAttribute . getUnit
      where
        toAttribute = from @AttributePattern . unitAttribute

toUnit :: symbol -> Unit symbol
toUnit sym = Unit { getUnit = Just sym }

fromUnit :: Unit symbol -> symbol
fromUnit Unit {getUnit = Just sym} = sym
fromUnit _ = error "There is no unit symbol to extract"

-- | Kore identifier representing the @unit@ attribute symbol.
unitId :: Id
unitId = "unit"

-- | Kore symbol representing the @unit@ attribute.
unitSymbol :: SymbolOrAlias
unitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = unitId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @unit@ attribute.
unitAttribute :: SymbolOrAlias -> AttributePattern
unitAttribute symbol = attributePattern unitSymbol [attributePattern_ symbol]
