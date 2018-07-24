{-|
Module      : Kore.Step.PatternAttributesError
Description : Data types and tools for errors related to pattern attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.PatternAttributesError
    ( FunctionError(..)
    , FunctionalError (..)
    ) where

import Kore.AST.Common
       ( SymbolOrAlias )

data FunctionError level
    = NonFunctionHead (SymbolOrAlias level)
    | NonFunctionPattern
    deriving (Eq, Show)

data FunctionalError level
    = NonFunctionalHead (SymbolOrAlias level)
    | NonFunctionalPattern
    deriving (Eq, Show)
