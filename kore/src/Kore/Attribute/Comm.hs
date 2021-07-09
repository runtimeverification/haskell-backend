{- |
Module      : Kore.Attribute.Comm
Description : Commutativity axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Comm (
    Comm (..),
    commId,
    commSymbol,
    commAttribute,
) where

import Data.Default
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @Comm@ represents the @comm@ attribute for axioms.
newtype Comm = Comm {isComm :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Comm where
    def = Comm False

-- | Kore identifier representing the @comm@ attribute symbol.
commId :: Id
commId = "comm"

-- | Kore symbol representing the @comm@ attribute.
commSymbol :: SymbolOrAlias
commSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = commId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @comm@ attribute.
commAttribute :: AttributePattern
commAttribute = attributePattern_ commSymbol

instance ParseAttributes Comm where
    parseAttribute = parseBoolAttribute commId

instance From Comm Attributes where
    from = toBoolAttributes commAttribute
