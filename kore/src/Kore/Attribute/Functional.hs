{-|
Module      : Kore.Attribute.Functional
Description : Functional symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Functional
    ( Functional (..)
    , functionalId, functionalSymbol, functionalAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Functional@ represents the @functional@ attribute for symbols.

Note: This attribute is also used to annotate axioms stating functionality
constraints.
 -}
newtype Functional = Functional { isDeclaredFunctional :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Semigroup Functional where
    (<>) (Functional a) (Functional b) = Functional (a || b)

instance Monoid Functional where
    mempty = Functional False

instance Default Functional where
    def = mempty

instance NFData Functional

instance SOP.Generic Functional

instance SOP.HasDatatypeInfo Functional

instance Debug Functional

instance Diff Functional

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
    toAttributes = toBoolAttributes functionalAttribute
