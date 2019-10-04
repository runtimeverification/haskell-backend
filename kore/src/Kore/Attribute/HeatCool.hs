{-|
Module      : Kore.Attribute.HeatCool
Description : Heating and Cooling axiom attribute
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
    ( NFData
    )
import Control.Monad
    ( (>=>)
    )
import Data.Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | Denote the heating or cooling phase of execution.

 -}
data HeatCool = Heat | Normal | Cool
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic HeatCool

instance SOP.HasDatatypeInfo HeatCool

instance Debug HeatCool

instance Diff HeatCool

instance NFData HeatCool

instance Default HeatCool where
    def = Normal

-- | Kore identifier representing the @heat@ attribute symbol.
heatId :: Id
heatId = "heat"

-- | Kore symbol representing the @heat@ attribute.
heatSymbol :: SymbolOrAlias
heatSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = heatId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @heat@ attribute.
heatAttribute :: AttributePattern
heatAttribute = attributePattern_ heatSymbol

-- | Kore identifier representing the @cool@ attribute symbol.
coolId :: Id
coolId = "cool"

-- | Kore symbol representing the @cool@ attribute.
coolSymbol :: SymbolOrAlias
coolSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = coolId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @cool@ attribute.
coolAttribute :: AttributePattern
coolAttribute = attributePattern_ coolSymbol

instance ParseAttributes HeatCool where
    parseAttribute attr =
        parseHeat attr >=> parseCool attr
      where
        parseHeat =
            withApplication' $ \params args heatCool -> do
                Parser.getZeroParams params
                Parser.getZeroArguments args
                case heatCool of
                    Normal -> return Heat
                    Heat -> failDuplicate'
                    Cool -> failConflicting'
          where
            withApplication' = Parser.withApplication heatId
            failDuplicate' = Parser.failDuplicate heatId
            failConflicting' = Parser.failConflicting [coolId, heatId]
        parseCool =
            withApplication' $ \params args heatCool -> do
                Parser.getZeroParams params
                Parser.getZeroArguments args
                case heatCool of
                    Normal -> return Cool
                    Cool -> failDuplicate'
                    Heat -> failConflicting'
          where
            withApplication' = Parser.withApplication coolId
            failDuplicate' = Parser.failDuplicate coolId
            failConflicting' = Parser.failConflicting [heatId, coolId]

    toAttributes Heat = Attributes [heatAttribute]
    toAttributes Cool = Attributes [coolAttribute]
    toAttributes Normal = def
