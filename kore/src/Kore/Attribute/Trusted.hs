{-|
Module      : Kore.Attribute.Trusted
Description : Attribute identifying trusted claim sentences
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com


A trusted claim is a reachability logic verification claim
which can be used as a circularity without needing to be proven.

-}
{-# LANGUAGE Strict #-}
module Kore.Attribute.Trusted
    ( Trusted (..)
    , trustedId, trustedSymbol, trustedAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Trusted@ represents the @trusted@ attribute for claim sentences.
 -}
newtype Trusted = Trusted { isTrusted :: Bool }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Trusted where
    def = Trusted False

-- | Kore identifier representing the @trusted@ attribute symbol.
trustedId :: Id
trustedId = "trusted"

-- | Kore symbol representing the @trusted@ attribute.
trustedSymbol :: SymbolOrAlias
trustedSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = trustedId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @trusted@ attribute.
trustedAttribute :: AttributePattern
trustedAttribute = attributePattern_ trustedSymbol

instance ParseAttributes Trusted where
    parseAttribute = parseBoolAttribute trustedId

instance From Trusted Attributes where
    from = toBoolAttributes trustedAttribute
