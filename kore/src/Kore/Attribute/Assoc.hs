{- |
Module      : Kore.Attribute.Assoc
Description : Associativity axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Assoc (
    Assoc (..),
    assocId,
    assocSymbol,
    assocAttribute,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @Assoc@ represents the @assoc@ attribute for axioms.
newtype Assoc = Assoc {isAssoc :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Assoc where
    def = Assoc False

-- | Kore identifier representing the @assoc@ attribute symbol.
assocId :: Id
assocId = "assoc"

-- | Kore symbol representing the @assoc@ attribute.
assocSymbol :: SymbolOrAlias
assocSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = assocId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @assoc@ attribute.
assocAttribute :: AttributePattern
assocAttribute = attributePattern_ assocSymbol

instance ParseAttributes Assoc where
    parseAttribute = parseBoolAttribute assocId

instance From Assoc Attributes where
    from = toBoolAttributes assocAttribute
