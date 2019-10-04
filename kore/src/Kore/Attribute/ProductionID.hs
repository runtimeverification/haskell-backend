{-|
Module      : Kore.Attribute.ProductionID
Description : Production ID attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.ProductionID
    ( ProductionID (..)
    , productionIDId, productionIDSymbol, productionIDAttribute
    ) where

import qualified Control.Monad as Monad
import qualified Data.Maybe as Maybe
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @ProductionID@ represents the @productionID@ attribute.
 -}
newtype ProductionID = ProductionID { getProductionID :: Maybe Text }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic ProductionID

instance SOP.HasDatatypeInfo ProductionID

instance Debug ProductionID

instance Diff ProductionID

instance NFData ProductionID

instance Default ProductionID where
    def = ProductionID Nothing

-- | Kore identifier representing the @productionID@ attribute symbol.
productionIDId :: Id
productionIDId = "productionID"

-- | Kore symbol representing the @productionID@ attribute.
productionIDSymbol :: SymbolOrAlias
productionIDSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = productionIDId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing a @productionID@ attribute.
productionIDAttribute :: Text -> AttributePattern
productionIDAttribute name =
    attributePattern productionIDSymbol [attributeString name]

instance ParseAttributes ProductionID where
    parseAttribute =
        withApplication' $ \params args (ProductionID productionID) -> do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            StringLiteral name <- Parser.getStringLiteral arg
            Monad.unless (Maybe.isNothing productionID) failDuplicate'
            return ProductionID { getProductionID = Just name }
      where
        withApplication' = Parser.withApplication productionIDId
        failDuplicate' = Parser.failDuplicate productionIDId

    toAttributes =
        maybe def toAttribute . getProductionID
      where
        toAttribute = Attributes . (: []) . productionIDAttribute
