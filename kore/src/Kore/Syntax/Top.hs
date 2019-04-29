{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Top where

import Control.DeepSeq
       ( NFData (..) )
import Data.Deriving
       ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import Data.Function
       ( on )
import Data.Functor.Classes
import Data.Hashable
import GHC.Generics
       ( Generic )

import Kore.Sort
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'topSort' is the sort of the result.

This represents the ⌈TopPattern⌉ Matching Logic construct.
-}
newtype Top level child = Top { topSort :: Sort}
    deriving (Functor, Foldable, Show, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Top level) where
    liftEq = $(makeLiftEq ''Top)

instance Ord1 (Top level) where
    liftCompare = $(makeLiftCompare ''Top)

instance Show1 (Top level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Top)

instance Eq (Top level child) where
    (==) = on (==) topSort

instance Ord (Top level child) where
    compare = on compare topSort

instance Hashable (Top level child)

instance NFData (Top level child)

instance Unparse (Top level child) where
    unparse Top { topSort } = "\\top" <> parameters [topSort] <> noArguments

    unparse2 _ = "\\top"
