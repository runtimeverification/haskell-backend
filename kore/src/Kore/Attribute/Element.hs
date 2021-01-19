{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Attribute.Element
    ( Element (..)
    , elementId, elementSymbol, elementAttribute
    ) where

import Prelude.Kore

import Data.Default
import qualified Generics.SOP as SOP

import Kore.Attribute.Parser
import Kore.Debug

-- | @Element@ represents the @element@ attribute.
newtype Element = Element { getElement :: Maybe SymbolOrAlias }
    deriving (Generic, Eq, Ord, Show)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

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

instance From Element Attributes where
    from =
        maybe def toAttribute . getElement
      where
        toAttribute = from @AttributePattern . elementAttribute
