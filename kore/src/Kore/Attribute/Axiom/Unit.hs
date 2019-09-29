{-|
Module      : Kore.Attribute.Axiom.Unit
Description : Unit axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Axiom.Unit
    ( Unit (..)
    , unitId, unitSymbol, unitAttribute
    ) where

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Unit@ represents the @unit@ attribute for axioms.
 -}
newtype Unit = Unit { isUnit :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Unit

instance SOP.HasDatatypeInfo Unit

instance Debug Unit

instance Diff Unit

instance NFData Unit

instance Default Unit where
    def = Unit False

-- | Kore identifier representing the @unit@ attribute symbol.
unitId :: Id
unitId = "unit"

-- | Kore symbol representing the @unit@ attribute.
unitSymbol :: SymbolOrAlias
unitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = unitId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @unit@ attribute.
unitAttribute :: AttributePattern
unitAttribute = attributePattern_ unitSymbol

instance ParseAttributes Unit where
    parseAttribute =
        withApplication' $ \params args Unit { isUnit } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isUnit failDuplicate'
            return Unit { isUnit = True }
      where
        withApplication' = Parser.withApplication unitId
        failDuplicate' = Parser.failDuplicate unitId

    toAttributes Unit { isUnit } = Attributes [unitAttribute | isUnit]
