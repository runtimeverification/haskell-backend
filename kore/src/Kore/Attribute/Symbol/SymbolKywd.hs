{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Symbol.SymbolKywd
    ( SymbolKywd (..)
    , symbolKywdId, symbolKywdSymbol, symbolKywdAttribute
    ) where

import Prelude.Kore

import Data.Monoid
    ( Any (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @SymbolKywd@ represents the @symbolKywd@ attribute for symbols.
newtype SymbolKywd = SymbolKywd { isSymbolKywd :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)
    deriving (Semigroup, Monoid) via Any

instance Default SymbolKywd where
    def = mempty

instance NFData SymbolKywd

instance SOP.Generic SymbolKywd

instance SOP.HasDatatypeInfo SymbolKywd

instance Debug SymbolKywd

instance Diff SymbolKywd

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
    toAttributes = toBoolAttributes symbolKywdAttribute
