{-|
Module      : Kore.Attribute.Sort.Concat
Description : Concat sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Concat
    ( Concat (..)
    , concatId, concatSymbol, concatAttribute
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Default
import GHC.Generics
    ( Generic
    )

import Kore.Attribute.Parser

-- | @Concat@ represents the @concat@ attribute for sorts.
newtype Concat = Concat { getConcat :: Maybe SymbolOrAlias }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Concat where
    (<>) a@(Concat (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Concat where
    mempty = Concat { getConcat = Nothing }

instance Default Concat where
    def = mempty

instance NFData Concat

instance ParseAttributes Concat where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Concat { getConcat }
          | Just _ <- getConcat = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Concat { getConcat = Just symbol }
        withApplication' = withApplication concatId
        failDuplicate' = failDuplicate concatId

    toAttributes =
        maybe def toAttribute . getConcat
      where
        toAttribute = Attributes . (: []) . concatAttribute

-- | Kore identifier representing the @concat@ attribute symbol.
concatId :: Id
concatId = "concat"

-- | Kore symbol representing the @concat@ attribute.
concatSymbol :: SymbolOrAlias
concatSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = concatId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @concat@ attribute.
concatAttribute :: SymbolOrAlias -> AttributePattern
concatAttribute symbol =
    attributePattern concatSymbol [attributePattern_ symbol]
