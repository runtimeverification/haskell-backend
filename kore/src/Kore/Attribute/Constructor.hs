{- |
Module      : Kore.Attribute.Constructor
Description : Constructor symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Constructor (
    Constructor (..),
    constructorId,
    constructorSymbol,
    constructorAttribute,
) where

import qualified Data.Monoid as Monoid
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

-- | @Constructor@ represents the @constructor@ attribute for symbols.
newtype Constructor = Constructor {isConstructor :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via Monoid.Any

instance Default Constructor where
    def = mempty

-- | Kore identifier representing the @constructor@ attribute symbol.
constructorId :: Id
constructorId = "constructor"

-- | Kore symbol representing the @constructor@ attribute.
constructorSymbol :: SymbolOrAlias
constructorSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = constructorId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @constructor@ attribute.
constructorAttribute :: AttributePattern
constructorAttribute = attributePattern_ constructorSymbol

instance ParseAttributes Constructor where
    parseAttribute = parseBoolAttribute constructorId

instance From Constructor Attributes where
    from = toBoolAttributes constructorAttribute
