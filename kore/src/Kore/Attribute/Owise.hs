{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Attribute.Owise (
    Owise (..),
    owiseId,
    owiseSymbol,
    owiseAttribute,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

newtype Owise = Owise {isOwise :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Owise where
    def = Owise False

owiseId :: Id
owiseId = "owise"

owiseSymbol :: SymbolOrAlias
owiseSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = owiseId
        , symbolOrAliasParams = []
        }

owiseAttribute :: AttributePattern
owiseAttribute = attributePattern_ owiseSymbol

instance ParseAttributes Owise where
    parseAttribute = parseBoolAttribute owiseId

instance From Owise Attributes where
    from = toBoolAttributes owiseAttribute
