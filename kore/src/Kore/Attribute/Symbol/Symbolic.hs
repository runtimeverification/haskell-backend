{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Attribute.Symbol.Symbolic
    ( Symbolic (..)
    , symbolicId
    , symbolicSymbol
    , symbolicAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

newtype Symbolic = Symbolic { isSymbolic :: Bool }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Symbolic where
    def = Symbolic False

symbolicId :: Id
symbolicId = "symbolic"

symbolicSymbol :: SymbolOrAlias
symbolicSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = symbolicId
        , symbolOrAliasParams = []
        }

symbolicAttribute :: AttributePattern
symbolicAttribute = attributePattern_ symbolicSymbol

instance ParseAttributes Symbolic where
    parseAttribute = parseBoolAttribute symbolicId

instance From Symbolic Attributes where
    from = toBoolAttributes symbolicAttribute
