{-|
Module      : Kore.Attribute.Sort.Unit
Description : Unit sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Unit
    ( Unit (..)
    , unitId, unitSymbol, unitAttribute
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import GHC.Generics
       ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

-- | @Unit@ represents the @unit@ attribute for sorts.
newtype Unit = Unit { getUnit :: Maybe (SymbolOrAlias Object) }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Unit where
    (<>) a@(Unit (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Unit where
    mempty = Unit { getUnit = Nothing }

instance Default Unit where
    def = mempty

instance NFData Unit

-- | Kore identifier representing the @unit@ attribute symbol.
unitId :: Id Object
unitId = "unit"

-- | Kore symbol representing the @unit@ attribute.
unitSymbol :: SymbolOrAlias Object
unitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = unitId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @unit@ attribute.
unitAttribute
    :: SymbolOrAlias Object
    -> CommonKorePattern
unitAttribute symbol =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = unitSymbol
            , applicationChildren =
                [ (asCommonKorePattern . ApplicationPattern)
                    Application
                        { applicationSymbolOrAlias = symbol
                        , applicationChildren = []
                        }
                ]
            }

instance ParseAttributes Unit where
    parseAttribute = withApplication parseApplication
      where
        parseApplication params args Unit { getUnit }
          | Just _ <- getUnit = failDuplicate
          | otherwise = do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            symbol <- Parser.getSymbolOrAlias arg
            return Unit { getUnit = Just symbol }
        withApplication = Parser.withApplication unitId
        failDuplicate = Parser.failDuplicate unitId
