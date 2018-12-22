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

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import qualified Data.Maybe as Maybe
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @ProductionID@ represents the @productionID@ attribute.
 -}
newtype ProductionID = ProductionID { getProductionID :: Maybe Text }
    deriving (Eq, Ord, Show, Generic)

instance NFData ProductionID

instance Default ProductionID where
    def = ProductionID Nothing

-- | Kore identifier representing the @productionID@ attribute symbol.
productionIDId :: Id Object
productionIDId = "productionID"

-- | Kore symbol representing the @productionID@ attribute.
productionIDSymbol :: SymbolOrAlias Object
productionIDSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = productionIDId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing a @productionID@ attribute.
productionIDAttribute :: Text -> CommonKorePattern
productionIDAttribute name =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = productionIDSymbol
            , applicationChildren =
                [ (asCommonKorePattern . StringLiteralPattern)
                    (StringLiteral $ Text.unpack name)
                ]
            }

instance ParseAttributes ProductionID where
    parseAttribute =
        withApplication $ \params args (ProductionID productionID) -> do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            StringLiteral name <- Parser.getStringLiteral arg
            Monad.unless (Maybe.isNothing productionID) failDuplicate
            return ProductionID { getProductionID = Just (Text.pack name) }
      where
        withApplication = Parser.withApplication productionIDId
        failDuplicate = Parser.failDuplicate productionIDId
