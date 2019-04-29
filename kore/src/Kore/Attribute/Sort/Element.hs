{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Attribute.Sort.Element
    ( Element (..)
    , elementId, elementSymbol, elementAttribute
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import GHC.Generics
       ( Generic )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.Attribute.Parser

-- | @Element@ represents the @element@ attribute for sorts.
newtype Element = Element { getElement :: Maybe (SymbolOrAlias Object) }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Element where
    (<>) a@(Element (Just _))  _ = a
    (<>) _                     b = b

instance Monoid Element where
    mempty = Element { getElement = Nothing }

instance Default Element where
    def = mempty

instance NFData Element

-- | Kore identifier representing the @element@ attribute symbol.
elementId :: Id Object
elementId = "element"

-- | Kore symbol representing the @element@ attribute.
elementSymbol :: SymbolOrAlias Object
elementSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = elementId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @element@ attribute.
elementAttribute :: SymbolOrAlias Object -> AttributePattern
elementAttribute symbol =
    attributePattern elementSymbol [attributePattern_ symbol]

instance ParseAttributes Element where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Element { getElement }
          | Just _ <- getElement = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Element { getElement = Just symbol }
        withApplication' = withApplication elementId
        failDuplicate' = failDuplicate elementId
