{-|
Module      : Kore.Attribute.Sort.Unit
Description : Unit sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Unit
    ( Unit (..)
    , unitId, unitSymbol, unitAttribute
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Default
import GHC.Generics
    ( Generic
    )

import Kore.Attribute.Parser

-- | @Unit@ represents the @unit@ attribute for sorts.
newtype Unit = Unit { getUnit :: Maybe SymbolOrAlias }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Unit where
    (<>) a@(Unit (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Unit where
    mempty = Unit { getUnit = Nothing }

instance Default Unit where
    def = mempty

instance NFData Unit

instance ParseAttributes Unit where
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

    toAttributes =
        maybe def toAttribute . getUnit
      where
        toAttribute = Attributes . (: []) . unitAttribute

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
