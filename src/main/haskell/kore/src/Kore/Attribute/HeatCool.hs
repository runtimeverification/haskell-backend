{-|
Module      : Kore.Attribute.HeatCool
Description : Associativity axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.HeatCool
    ( HeatCool (..)
    , heatId, heatSymbol, heatAttribute
    , coolId, coolSymbol, coolAttribute
    ) where

import Control.DeepSeq
       ( NFData )
import Control.Monad
       ( (>=>) )
import Data.Default
import GHC.Generics
       ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | Denote the heating or cooling phase of execution.

 -}
data HeatCool = Heat | Normal | Cool
    deriving (Eq, Ord, Show, Generic)

instance NFData HeatCool

instance Default HeatCool where
    def = Normal

-- | Kore identifier representing the @heat@ attribute symbol.
heatId :: Id Object
heatId = "heat"

-- | Kore symbol representing the @heat@ attribute.
heatSymbol :: SymbolOrAlias Object
heatSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = heatId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @heat@ attribute.
heatAttribute :: CommonKorePattern
heatAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = heatSymbol
            , applicationChildren = []
            }

-- | Kore identifier representing the @cool@ attribute symbol.
coolId :: Id Object
coolId = "cool"

-- | Kore symbol representing the @cool@ attribute.
coolSymbol :: SymbolOrAlias Object
coolSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = coolId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @cool@ attribute.
coolAttribute :: CommonKorePattern
coolAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = coolSymbol
            , applicationChildren = []
            }

instance ParseAttributes HeatCool where
    parseAttribute attr =
        parseHeat attr >=> parseCool attr
      where
        parseHeat =
            withApplication $ \params args heatCool -> do
                Parser.getZeroParams params
                Parser.getZeroArguments args
                case heatCool of
                    Normal -> return Heat
                    Heat -> failDuplicate
                    Cool -> failConflicting
          where
            withApplication = Parser.withApplication heatId
            failDuplicate = Parser.failDuplicate heatId
            failConflicting = Parser.failConflicting [coolId, heatId]
        parseCool =
            withApplication $ \params args heatCool -> do
                Parser.getZeroParams params
                Parser.getZeroArguments args
                case heatCool of
                    Normal -> return Cool
                    Cool -> failDuplicate
                    Heat -> failConflicting
          where
            withApplication = Parser.withApplication coolId
            failDuplicate = Parser.failDuplicate coolId
            failConflicting = Parser.failConflicting [heatId, coolId]
