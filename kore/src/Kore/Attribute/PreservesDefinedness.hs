{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Attribute.PreservesDefinedness (
    PreservesDefinedness (..),
    preservesDefinednessId,
    preservesDefinednessSymbol,
    preservesDefinednessAttribute,
) where

import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

newtype PreservesDefinedness = PreservesDefinedness {doesPreserveDefinedness :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving anyclass (Hashable)

instance Default PreservesDefinedness where
    def = PreservesDefinedness False

preservesDefinednessId :: Id
preservesDefinednessId = "preservesDefinedness"

preservesDefinednessSymbol :: SymbolOrAlias
preservesDefinednessSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = preservesDefinednessId
        , symbolOrAliasParams = []
        }

preservesDefinednessAttribute :: AttributePattern
preservesDefinednessAttribute = attributePattern_ preservesDefinednessSymbol

instance ParseAttributes PreservesDefinedness where
    parseAttribute = parseBoolAttribute preservesDefinednessId

instance From PreservesDefinedness Attributes where
    from = toBoolAttributes preservesDefinednessAttribute
