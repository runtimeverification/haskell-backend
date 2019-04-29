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
import           Data.Text
                 ( Text )

import Kore.Attribute.Parser as Parser

{- | @ProductionID@ represents the @productionID@ attribute.
 -}
newtype ProductionID = ProductionID { getProductionID :: Maybe Text }
    deriving (Eq, Ord, Show, Generic)

instance NFData ProductionID

instance Default ProductionID where
    def = ProductionID Nothing

-- | Kore identifier representing the @productionID@ attribute symbol.
productionIDId :: Id
productionIDId = "productionID"

-- | Kore symbol representing the @productionID@ attribute.
productionIDSymbol :: SymbolOrAlias Object
productionIDSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = productionIDId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing a @productionID@ attribute.
productionIDAttribute :: Text -> AttributePattern
productionIDAttribute name =
    attributePattern productionIDSymbol
        [ (asAttributePattern . StringLiteralPattern) (StringLiteral name) ]

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
