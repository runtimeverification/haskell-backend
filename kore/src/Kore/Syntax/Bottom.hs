{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Bottom
    ( Bottom (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Functor.Classes
import           Data.Hashable
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

{-|'Bottom' corresponds to the @\bottom@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'bottomSort' is the sort of the result.

This represents the ⌈BottomPattern⌉ Matching Logic construct.
-}
newtype Bottom level child = Bottom { bottomSort :: Sort }
    deriving (Eq, Functor, Foldable, Generic, Ord, Traversable, Show)

$newDefinitionGroup

instance Eq1 (Bottom level) where
    liftEq = $(Deriving.makeLiftEq ''Bottom)

instance Ord1 (Bottom level) where
    liftCompare = $(Deriving.makeLiftCompare ''Bottom)

instance Show1 (Bottom level) where
    liftShowsPrec = $(Deriving.makeLiftShowsPrec ''Bottom)

instance Hashable (Bottom level child)

instance NFData (Bottom level child)

instance Unparse (Bottom level child) where
    unparse Bottom { bottomSort } =
        "\\bottom" <> parameters [bottomSort] <> noArguments
    unparse2 _ = "\\bottom"
