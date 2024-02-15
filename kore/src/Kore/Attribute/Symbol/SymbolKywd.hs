{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Attribute.Symbol.SymbolKywd (
    SymbolKywd (..),
    symbolKywdId,
    symbolKywdSymbol,
    symbolKywdAttribute,
) where

import Data.Text (Text)
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @SymbolKywd@ represents the @symbolKywd@ attribute for symbols.
-- FIXME change this to hold an optional Text (see kLabel), use sites can check emptiness
newtype SymbolKywd = SymbolKywd {getSymbol :: Maybe Text}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default SymbolKywd where
    def = SymbolKywd Nothing

-- | Kore identifier representing the @symbolKywd@ attribute symbol.
symbolKywdId :: Id
symbolKywdId = "symbol'Kywd'"

-- | Kore symbol representing the @symbolKywd@ attribute.
symbolKywdSymbol :: SymbolOrAlias
symbolKywdSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = symbolKywdId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @symbolKywd@ attribute.
symbolKywdAttribute :: Text -> AttributePattern
symbolKywdAttribute = attributePattern symbolKywdSymbol . (:[]) . attributeString

instance ParseAttributes SymbolKywd where
    -- if an argument is present, use it for the contents, otherwise 
    -- leave it empty (but present) to signal presence of the attribute.
    parseAttribute =
        withApplication symbolKywdId $ \params args SymbolKywd{getSymbol} -> do
            Parser.getZeroParams params
            mbArg <- Parser.getZeroOrOneArguments args
            unless (isNothing getSymbol) $ failDuplicate symbolKywdId
            StringLiteral arg <- maybe (pure $ StringLiteral "") getStringLiteral mbArg
            pure $ SymbolKywd (Just arg)

instance From SymbolKywd Attributes where
    from =
        maybe def (from @AttributePattern . symbolKywdAttribute) . getSymbol
