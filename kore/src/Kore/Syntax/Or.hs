{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Or where

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

{-|'Or' corresponds to the @\or@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'orSort' is both the sort of the operands and the sort of the result.

This represents the 'orFirst ∨ orSecond' Matching Logic construct.
-}
data Or level child = Or
    { orSort   :: !Sort
    , orFirst  :: child
    , orSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Or level) where
    liftEq = $(makeLiftEq ''Or)

instance Ord1 (Or level) where
    liftCompare = $(makeLiftCompare ''Or)

instance Show1 (Or level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Or)

instance Eq child => Eq (Or level child) where
    (==) = eq1

instance Ord child => Ord (Or level child) where
    compare = compare1

instance Show child => Show (Or level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Or level child)

instance NFData child => NFData (Or level child)

instance Unparse child => Unparse (Or level child) where
    unparse Or { orSort, orFirst, orSecond } =
        "\\or"
        <> parameters [orSort]
        <> arguments [orFirst, orSecond]

    unparse2 Or { orFirst, orSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\or"
            , unparse2 orFirst
            , unparse2 orSecond
            ])
