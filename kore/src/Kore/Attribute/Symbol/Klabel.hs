{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Symbol.Klabel
    ( Klabel (..)
    , klabelId, klabelSymbol, klabelAttribute
    ) where

import Prelude.Kore

import qualified Control.Monad as Monad
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @Klabel@ represents the @klabel@ attribute for symbols.
newtype Klabel = Klabel { getKlabel :: Maybe Text }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Default Klabel where
    def = Klabel Nothing

instance NFData Klabel

instance SOP.Generic Klabel

instance SOP.HasDatatypeInfo Klabel

instance Debug Klabel

instance Diff Klabel

-- | Kore identifier representing the @klabel@ attribute symbol.
klabelId :: Id
klabelId = "klabel"

-- | Kore symbol representing the @klabel@ attribute.
klabelSymbol :: SymbolOrAlias
klabelSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = klabelId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @klabel@ attribute.
klabelAttribute :: Text -> AttributePattern
klabelAttribute name =
    attributePattern klabelSymbol [attributeString name]

instance ParseAttributes Klabel where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Klabel { getKlabel } = do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            StringLiteral name <- Parser.getStringLiteral arg
            Monad.unless (isNothing getKlabel) failDuplicate'
            return Klabel { getKlabel = Just name }
        withApplication' = Parser.withApplication klabelId
        failDuplicate' = Parser.failDuplicate klabelId

    toAttributes =
        maybe def toAttribute . getKlabel
      where
        toAttribute = Attributes . (: []) . klabelAttribute
