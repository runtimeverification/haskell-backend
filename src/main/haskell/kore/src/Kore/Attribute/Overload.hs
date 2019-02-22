{-|
Module      : Kore.Attribute.Overload
Description : Overloaded production attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Overload
    ( Overload (..)
    , overloadId, overloadSymbol, overloadAttribute
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

-- | @Overload@ represents the @overload@ attribute for symbols.
newtype Overload =
    Overload
        { getOverload :: Maybe (SymbolOrAlias Object, SymbolOrAlias Object) }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Overload where
    (<>) a@(Overload (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Overload where
    mempty = Overload { getOverload = Nothing }

instance Default Overload where
    def = mempty

instance NFData Overload

-- | Kore identifier representing the @overload@ attribute symbol.
overloadId :: Id Object
overloadId = "overload"

-- | Kore symbol representing the @overload@ attribute.
overloadSymbol :: SymbolOrAlias Object
overloadSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = overloadId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @overload@ attribute.
overloadAttribute
    :: SymbolOrAlias Object
    -> SymbolOrAlias Object
    -> CommonKorePattern
overloadAttribute symbol1 symbol2 =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = overloadSymbol
            , applicationChildren =
                [ (asCommonKorePattern . ApplicationPattern)
                    Application
                        { applicationSymbolOrAlias = symbol1
                        , applicationChildren = []
                        }
                , (asCommonKorePattern . ApplicationPattern)
                    Application
                        { applicationSymbolOrAlias = symbol2
                        , applicationChildren = []
                        }
                ]
            }

instance ParseAttributes Overload where
    parseAttribute = withApplication parseApplication
      where
        parseApplication params args Overload { getOverload }
          | Just _ <- getOverload = failDuplicate
          | otherwise = do
            Parser.getZeroParams params
            (arg1, arg2) <- Parser.getTwoArguments args
            symbol1 <- Parser.getSymbolOrAlias arg1
            symbol2 <- Parser.getSymbolOrAlias arg2
            return Overload { getOverload = Just (symbol1, symbol2) }
        withApplication = Parser.withApplication overloadId
        failDuplicate = Parser.failDuplicate overloadId
