{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.And
    ( And (..)
    ) where

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

{-|'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And level child = And
    { andSort   :: !Sort
    , andFirst  :: child
    , andSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (And level) where
    liftEq = $(makeLiftEq ''And)

instance Ord1 (And level) where
    liftCompare = $(makeLiftCompare ''And)

instance Show1 (And level) where
    liftShowsPrec = $(makeLiftShowsPrec ''And)

instance Eq child => Eq (And level child) where
    (==) = eq1

instance Ord child => Ord (And level child) where
    compare = compare1

instance Show child => Show (And level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (And level child)

instance NFData child => NFData (And level child)

instance Unparse child => Unparse (And level child) where
    unparse
        And { andSort, andFirst, andSecond }
      =
        "\\and"
        <> parameters [andSort]
        <> arguments [andFirst, andSecond]

    unparse2
        And { andFirst, andSecond }
      = Pretty.parens (Pretty.fillSep
            [ "\\and"
            , unparse2 andFirst
            , unparse2 andSecond
            ])
