{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Attribute.Symbol.SymbolKywd (
    SymbolKywd (..),
    symbolKywdId,
    symbolKywdSymbol,
    symbolKywdAttribute,
) where

import Data.Monoid (
    Any (..),
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @SymbolKywd@ represents the @symbolKywd@ attribute for symbols.
newtype SymbolKywd = SymbolKywd {isSymbolKywd :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via Any

instance Default SymbolKywd where
    def = mempty

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
symbolKywdAttribute :: AttributePattern
symbolKywdAttribute = attributePattern_ symbolKywdSymbol

instance ParseAttributes SymbolKywd where
    parseAttribute = parseBoolAttribute symbolKywdId

instance From SymbolKywd Attributes where
    from = toBoolAttributes symbolKywdAttribute
