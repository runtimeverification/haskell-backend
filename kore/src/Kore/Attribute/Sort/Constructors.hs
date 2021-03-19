{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
{-# LANGUAGE Strict #-}

module Kore.Attribute.Sort.Constructors
    ( Constructors (..)
    , ConstructorLike (..)
    , Constructor (..)
    ) where

import Prelude.Kore

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

{-| @Nothing@ means that the sort has no constructors that we can recognize.
@Just value@ means that we recognized the sort's constructors, and @value@
contains the list of these constructors.
-}
newtype Constructors =
    Constructors { getConstructors :: Maybe (NonEmpty ConstructorLike) }
    deriving (Show, Eq)
