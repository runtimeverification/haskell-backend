{- |
Module      : Kore.Attribute.Functional
Description : Functional symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Functional (
    Functional (..),
    functionalId,
    functionalSymbol,
    functionalAttribute,
) where

import qualified Data.Monoid as Monoid
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

{- | @Functional@ represents the @functional@ attribute for symbols.

Note: This attribute is also used to annotate axioms stating functionality
constraints.
-}
newtype Functional = Functional {isDeclaredFunctional :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via Monoid.Any

instance Default Functional where
    def = mempty

-- | Kore identifier representing the @functional@ attribute symbol.
functionalId :: Id
functionalId = "functional"

-- | Kore symbol representing the @functional@ attribute.
functionalSymbol :: SymbolOrAlias
functionalSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = functionalId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @functional@ attribute.
functionalAttribute :: AttributePattern
functionalAttribute = attributePattern_ functionalSymbol

instance ParseAttributes Functional where
    parseAttribute = parseBoolAttribute functionalId

instance From Functional Attributes where
    from = toBoolAttributes functionalAttribute
