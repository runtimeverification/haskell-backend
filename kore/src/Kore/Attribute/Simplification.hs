{-|
Module      : Kore.Attribute.Simplification
Description : Function simplification axiom attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com


The simplification attribute identifies axioms that are useful for
simplifying configurations, without being part of the main semantics.

Kore syntax: @simplification{}()@

Informal example of an axiom that would use the simplification attribute:

(x +Int y) +Int z = (x +Int z) +Int y
    if concrete(x) and concrete(z) and not concrete(y)
-}
module Kore.Attribute.Simplification
    ( Simplification (..)
    , simplificationId, simplificationSymbol, simplificationAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Simplification@ represents the @simplification@ attribute for axioms.
 -}
newtype Simplification = Simplification { isSimplification :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Simplification

instance SOP.HasDatatypeInfo Simplification

instance Debug Simplification

instance Diff Simplification

instance NFData Simplification

instance Default Simplification where
    def = Simplification False

-- | Kore identifier representing the @simplification@ attribute symbol.
simplificationId :: Id
simplificationId = "simplification"

-- | Kore symbol representing the @simplification@ attribute.
simplificationSymbol :: SymbolOrAlias
simplificationSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = simplificationId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @simplification@ attribute.
simplificationAttribute :: AttributePattern
simplificationAttribute = attributePattern_ simplificationSymbol

instance ParseAttributes Simplification where
    parseAttribute = parseBoolAttribute simplificationId

instance From Simplification Attributes where
    from = toBoolAttributes simplificationAttribute
