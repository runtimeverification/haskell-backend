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
    ( ConstructorLikeError (..)
    , FunctionError (..)
    , FunctionalError (..)
    , TotalError (..)
    ) where

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Internal.Symbol
    ( Symbol
    )

{-| An error explaining why a pattern is not composed of function heads and
things like StringLiteral, DomainValue and variables.
-}
data FunctionError
    = NonFunctionHead Symbol
    -- ^ The pattern was the application of a non-function head to something
    | NonFunctionPattern
    -- ^ The pattern is neither an application pattern nor one of the basic
    -- pattern types (e.g. domain values).
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic FunctionError

instance SOP.HasDatatypeInfo FunctionError

instance Debug FunctionError

instance Diff FunctionError

{-| An error explaining why a pattern is not composed of functional heads and
things like StringLiteral, DomainValue and variables.
-}
data FunctionalError
    = NonFunctionalHead Symbol
    -- ^ The pattern was the application of a non-functional head to something
    | NonFunctionalPattern
    -- ^ The pattern is neither an application pattern nor one of the basic
    -- pattern types (e.g. domain values).
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic FunctionalError

instance SOP.HasDatatypeInfo FunctionalError

instance Debug FunctionalError

instance Diff FunctionalError

{-| An error explaining why a pattern is not composed of constructor-like heads
and things like StringLiteral, DomainValue and variables.
-}
data ConstructorLikeError
    = NonConstructorLikeHead
    -- ^ The pattern was the application of a non-functional head to something
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic ConstructorLikeError

instance SOP.HasDatatypeInfo ConstructorLikeError

instance Debug ConstructorLikeError

instance Diff ConstructorLikeError

{-| An error explaining why a pattern is not composed of total heads and
things like StringLiteral, DomainValue and variables.
-}
data TotalError
    = NonTotalHead Symbol
    -- ^ The pattern was the application of a non-total head to something
    | NonTotalPattern
    -- ^ The pattern is neither an application pattern nor one of the basic
    -- pattern types (e.g. domain values).
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic TotalError

instance SOP.HasDatatypeInfo TotalError

instance Debug TotalError

instance Diff TotalError
