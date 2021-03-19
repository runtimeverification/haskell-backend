{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}
{-# LANGUAGE Strict #-}

module Kore.Attribute.Symbol.NoEvaluators
    ( NoEvaluators (..)
    , noEvaluatorsId, noEvaluatorsSymbol, noEvaluatorsAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

newtype NoEvaluators = NoEvaluators { hasNoEvaluators :: Bool }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
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
