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
    ( FunctionError (..)
    , FunctionalError (..)
    , TotalError (..)
    ) where

import GHC.Generics
       ( Generic )

import Kore.AST.Common
       ( SymbolOrAlias )
import Kore.Reflect
       ( Reflectable )

{-| An error explaining why a pattern is not composed of function heads and
things like StringLiteral, DomainValue and variables.
-}
data FunctionError level
    = NonFunctionHead (SymbolOrAlias level)
    -- ^ The pattern was the application of a non-function head to something
    | NonFunctionPattern
    -- ^ The pattern is neither an application pattern nor one of the basic
    -- pattern types (e.g. domain values).
    deriving (Eq, Generic, Show)

instance Reflectable (FunctionError level)

{-| An error explaining why a pattern is not composed of functional heads and
things like StringLiteral, DomainValue and variables.
-}
data FunctionalError level
    = NonFunctionalHead (SymbolOrAlias level)
    -- ^ The pattern was the application of a non-functional head to something
    | NonFunctionalPattern
    -- ^ The pattern is neither an application pattern nor one of the basic
    -- pattern types (e.g. domain values).
    deriving (Eq, Generic, Show)

instance Reflectable (FunctionalError level)

{-| An error explaining why a pattern is not composed of total heads and
things like StringLiteral, DomainValue and variables.
-}
data TotalError level
    = NonTotalHead (SymbolOrAlias level)
    -- ^ The pattern was the application of a non-total head to something
    | NonTotalPattern
    -- ^ The pattern is neither an application pattern nor one of the basic
    -- pattern types (e.g. domain values).
    deriving (Eq, Show)
