{-|
Module      : Kore.Attribute.HasDomainValues
Description : Attribute saying whether a sort has domain values.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Attribute.Sort.HasDomainValues
    ( HasDomainValues (..)
    , hasDomainValuesId, hasDomainValuesSymbol, hasDomainValuesAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @HasDomainValues@ represents the @hasDomainValues@ attribute for symbols.
newtype HasDomainValues = HasDomainValues { getHasDomainValues :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Semigroup HasDomainValues where
    (<>) (HasDomainValues a) (HasDomainValues b) = HasDomainValues (a || b)

instance Monoid HasDomainValues where
    mempty = HasDomainValues False

instance Default HasDomainValues where
    def = mempty

instance NFData HasDomainValues

instance SOP.Generic HasDomainValues

instance SOP.HasDatatypeInfo HasDomainValues

instance Debug HasDomainValues

-- | Kore identifier representing the @hasDomainValues@ attribute symbol.
hasDomainValuesId :: Id
hasDomainValuesId = "hasDomainValues"

-- | Kore symbol representing the @hasDomainValues@ attribute.
hasDomainValuesSymbol :: SymbolOrAlias
hasDomainValuesSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = hasDomainValuesId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @hasDomainValues@ attribute.
hasDomainValuesAttribute :: AttributePattern
hasDomainValuesAttribute = attributePattern hasDomainValuesSymbol []

instance ParseAttributes HasDomainValues where
    parseAttribute = parseBoolAttribute hasDomainValuesId
    toAttributes = toBoolAttributes hasDomainValuesAttribute
