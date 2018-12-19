{-|
Module      : Kore.Attribute.Trusted
Description : Trusted claim sentence attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Trusted
    ( Trusted (..)
    , trustedId, trustedSymbol, trustedAttribute
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @Trusted@ represents the @trusted@ attribute for claim sentences.
 -}
newtype Trusted = Trusted { isTrusted :: Bool }
    deriving (Eq, Ord, Show, Generic)

instance NFData Trusted

instance Default Trusted where
    def = Trusted False

-- | Kore identifier representing the @trusted@ attribute symbol.
trustedId :: Id Object
trustedId = "trusted"

-- | Kore symbol representing the @trusted@ attribute.
trustedSymbol :: SymbolOrAlias Object
trustedSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = trustedId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @trusted@ attribute.
trustedAttribute :: CommonKorePattern
trustedAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = trustedSymbol
            , applicationChildren = []
            }

instance ParseAttributes Trusted where
    parseAttribute =
        withApplication $ \params args Trusted { isTrusted } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isTrusted failDuplicate
            return Trusted { isTrusted = True }
      where
        withApplication = Parser.withApplication trustedId
        failDuplicate = Parser.failDuplicate trustedId
