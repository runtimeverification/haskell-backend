{-|
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}

{-# LANGUAGE Strict #-}

module Kore.Attribute.Element
    ( Element (..)
    , mergeElement, toElement, fromElement
    , elementId, elementSymbol, elementAttribute
    ) where

import Prelude.Kore

import Data.Default
import qualified Generics.SOP as SOP

import Kore.Attribute.Parser
import Kore.Debug
import Kore.Unparser

-- | @Element@ represents the @element@ attribute.
newtype Element symbol = Element { getElement :: Maybe symbol }
    deriving (Generic, Eq, Ord, Show)
    deriving (Foldable, Functor, Traversable)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mergeElement
    :: (Eq symbol , Unparse symbol)
    => Element symbol
    -> Element symbol
    -> Element symbol
mergeElement (Element Nothing) b = b
mergeElement a (Element Nothing) = a
mergeElement a@(Element (Just aSymbol)) (Element (Just bSymbol))
      | aSymbol == bSymbol = a
      | otherwise = error $
        "Element symbol mismatch error! Found both "
        ++ unparseToString aSymbol
        ++ " and "
        ++ unparseToString bSymbol
        ++ " inside term.  This is a bug."

instance Default (Element symbol) where
    def = Element { getElement = Nothing }

instance NFData symbol => NFData (Element symbol)

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

instance ParseAttributes (Element SymbolOrAlias) where
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

instance From (Element SymbolOrAlias) Attributes where
    from =
        maybe def toAttribute . getElement
      where
        toAttribute = from @AttributePattern . elementAttribute

toElement :: symbol -> Element symbol
toElement sym = Element { getElement = Just sym }

fromElement :: Element symbol -> symbol
fromElement Element {getElement = Just sym} = sym
fromElement _ = error "There is no element symbol to extract"
