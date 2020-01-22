{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Attribute.Symbol.NoEvaluators
    ( NoEvaluators (..)
    , noEvaluatorsId, noEvaluatorsSymbol, noEvaluatorsAttribute
    ) where

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

newtype NoEvaluators = NoEvaluators { hasNoEvaluators :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Default NoEvaluators where
    def = NoEvaluators False

instance NFData NoEvaluators

instance SOP.Generic NoEvaluators

instance SOP.HasDatatypeInfo NoEvaluators

instance Debug NoEvaluators

instance Diff NoEvaluators

noEvaluatorsId :: Id
noEvaluatorsId = "noEvaluators"

noEvaluatorsSymbol :: SymbolOrAlias
noEvaluatorsSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = noEvaluatorsId
        , symbolOrAliasParams = []
        }

noEvaluatorsAttribute :: AttributePattern
noEvaluatorsAttribute = attributePattern_ noEvaluatorsSymbol

instance ParseAttributes NoEvaluators where
    parseAttribute = parseBoolAttribute noEvaluatorsId
    toAttributes = toBoolAttributes noEvaluatorsAttribute
