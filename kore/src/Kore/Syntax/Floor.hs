{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Floor where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import           Data.Functor.Classes
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

{-|'Floor' corresponds to the @\floor@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'floorOperandSort' is the sort of the operand.

'floorResultSort' is the sort of the result.

This represents the '⌊floorPattern⌋' Matching Logic construct.
-}
data Floor level child = Floor
    { floorOperandSort :: !Sort
    , floorResultSort  :: !Sort
    , floorChild       :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Floor level) where
    liftEq = $(makeLiftEq ''Floor)

instance Ord1 (Floor level) where
    liftCompare = $(makeLiftCompare ''Floor)

instance Show1 (Floor level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Floor)

instance Eq child => Eq (Floor level child) where
    (==) = eq1

instance Ord child => Ord (Floor level child) where
    compare = compare1

instance Show child => Show (Floor level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Floor level child)

instance NFData child => NFData (Floor level child)

instance Unparse child => Unparse (Floor level child) where
    unparse Floor { floorOperandSort, floorResultSort, floorChild } =
        "\\floor"
        <> parameters [floorOperandSort, floorResultSort]
        <> arguments [floorChild]

    unparse2 Floor { floorChild } =
        Pretty.parens (Pretty.fillSep ["\\floor", unparse2 floorChild])
