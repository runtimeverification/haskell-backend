{-|
Module      : Kore.Attribute.Trusted
Description : Attribute identifying trusted claim sentences
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com


A trusted claim is a reachability logic verification claim
which can be used as a circularity without needing to be proven.

-}
module Kore.Attribute.Trusted
    ( Trusted (..)
    , trustedId, trustedSymbol, trustedAttribute
    ) where

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Trusted@ represents the @trusted@ attribute for claim sentences.
 -}
newtype Trusted = Trusted { isTrusted :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Trusted

instance SOP.HasDatatypeInfo Trusted

instance Debug Trusted

instance Diff Trusted

instance NFData Trusted

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
    parseAttribute =
        withApplication' $ \params args Trusted { isTrusted } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isTrusted failDuplicate'
            return Trusted { isTrusted = True }
      where
        withApplication' = Parser.withApplication trustedId
        failDuplicate' = Parser.failDuplicate trustedId

    toAttributes Trusted { isTrusted } =
        Attributes [trustedAttribute | isTrusted]
