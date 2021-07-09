{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Attribute.Symbol.NoEvaluators (
    NoEvaluators (..),
    noEvaluatorsId,
    noEvaluatorsSymbol,
    noEvaluatorsAttribute,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Parser as Parser
import Kore.Debug
import Prelude.Kore

newtype NoEvaluators = NoEvaluators {hasNoEvaluators :: Bool}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default NoEvaluators where
    def = NoEvaluators False

noEvaluatorsId :: Id
noEvaluatorsId = "no-evaluators"

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

instance From NoEvaluators Attributes where
    from = toBoolAttributes noEvaluatorsAttribute
