{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Attribute.Sort.Element
    ( Element (..)
    , elementId, elementSymbol, elementAttribute
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Default
import GHC.Generics
    ( Generic
    )

import Kore.Attribute.Parser

-- | @Element@ represents the @element@ attribute for sorts.
newtype Element = Element { getElement :: Maybe SymbolOrAlias }
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
elementId :: Id
elementId = "element"

-- | Kore symbol representing the @element@ attribute.
elementSymbol :: SymbolOrAlias
elementSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = elementId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @element@ attribute.
elementAttribute :: SymbolOrAlias -> AttributePattern
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

    toAttributes =
        maybe def toAttribute . getElement
      where
        toAttribute = Attributes . (: []) . elementAttribute
