{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Attribute.Sort.Constructors
    ( Constructors (..)
    , ConstructorLike (..)
    , Constructor (..)
    ) where

import Data.List.NonEmpty
    ( NonEmpty
    )

import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Sort
    ( Sort
    )

data Constructor = Constructor
    { name :: !Symbol
    , sorts :: ![Sort]
    }
    deriving (Show, Eq)

data ConstructorLike =
    ConstructorLikeConstructor !Constructor
  | ConstructorLikeInjection
    deriving (Show, Eq)

newtype Constructors =
    Constructors { getConstructors :: Maybe (NonEmpty ConstructorLike) }
    deriving (Show, Eq)
