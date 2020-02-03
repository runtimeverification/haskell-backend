{-|
Module      : Kore.Attribute.Assoc
Description : Associativity axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Assoc
    ( Assoc (..)
    , assocId, assocSymbol, assocAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Assoc@ represents the @assoc@ attribute for axioms.
 -}
newtype Assoc = Assoc { isAssoc :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Assoc

instance SOP.HasDatatypeInfo Assoc

instance Debug Assoc

instance Diff Assoc

instance NFData Assoc

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
    toAttributes = toBoolAttributes assocAttribute
