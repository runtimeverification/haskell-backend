{-|
Module      : Kore.Attribute.UniqueId
License     : NCSA

The unique id attribute identifies symbols, sorts, axioms and
various other things.

Example:
@UNIQUE'Unds'ID{}("07a34b11585162c291311c03441e08beb2532e48d4ece33b9d58a9456f2f7623")@
-}
module Kore.Attribute.UniqueId
    ( UniqueId (..)
    , uniqueIdId
    , uniqueIdSymbol
    , uniqueIdAttribute
    ) where

import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as AttributeParser
import Kore.Debug

{- | @UniqueId@ represents the @uniqueId@ attribute for axioms.
 -}
newtype UniqueId = UniqueId { getUniqueId :: Maybe Text }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic UniqueId

instance SOP.HasDatatypeInfo UniqueId

instance Debug UniqueId

instance NFData UniqueId

instance Diff UniqueId

instance Default UniqueId where
    def = UniqueId Nothing

-- | Kore identifier representing the @uniqueId@ attribute symbol.
uniqueIdId :: Id
uniqueIdId = "UNIQUE'Unds'ID"

-- | Kore symbol representing the @uniqueId@ attribute.
uniqueIdSymbol :: SymbolOrAlias
uniqueIdSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = uniqueIdId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @uniqueId@ attribute.
uniqueIdAttribute :: Text -> AttributePattern
uniqueIdAttribute uniqueId =
    attributePattern uniqueIdSymbol [attributeString uniqueId]

instance ParseAttributes UniqueId where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication
            :: [Sort]
            -> [AttributePattern]
            -> UniqueId
            -> AttributeParser.Parser UniqueId
        parseApplication params args (UniqueId Nothing) = do
            AttributeParser.getZeroParams params
            arg <- AttributeParser.getOneArgument args
            StringLiteral str <- AttributeParser.getStringLiteral arg
            return (UniqueId (Just str))
        parseApplication _ _ (UniqueId (Just _)) = failDuplicate'

        withApplication' = AttributeParser.withApplication uniqueIdId
        failDuplicate' = AttributeParser.failDuplicate uniqueIdId

    toAttributes UniqueId { getUniqueId = Just uniqueId } =
        Attributes [uniqueIdAttribute uniqueId]
    toAttributes UniqueId { getUniqueId = Nothing } = Attributes []
