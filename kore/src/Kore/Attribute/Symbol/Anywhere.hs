{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Attribute.Symbol.Anywhere (
    Anywhere (..),
    anywhereId,
    anywhereSymbol,
    anywhereAttribute,
) where

import qualified Data.Monoid as Monoid
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @Anywhere@ represents the @anywhere@ attribute for symbols.
newtype Anywhere = Anywhere {isAnywhere :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via Monoid.Any

instance Default Anywhere where
    def = mempty

-- | Kore identifier representing the @anywhere@ attribute symbol.
anywhereId :: Id
anywhereId = "anywhere"

-- | Kore symbol representing the @anywhere@ attribute.
anywhereSymbol :: SymbolOrAlias
anywhereSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = anywhereId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @anywhere@ attribute.
anywhereAttribute :: AttributePattern
anywhereAttribute = attributePattern_ anywhereSymbol

instance ParseAttributes Anywhere where
    parseAttribute = parseBoolAttribute anywhereId

instance From Anywhere Attributes where
    from = toBoolAttributes anywhereAttribute
