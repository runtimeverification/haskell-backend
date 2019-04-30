{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Not where

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

{-|'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'notSort' is both the sort of the operand and the sort of the result.

-}
data Not level child = Not
    { notSort  :: !Sort
    , notChild :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Not level) where
    liftEq = $(makeLiftEq ''Not)

instance Ord1 (Not level) where
    liftCompare = $(makeLiftCompare ''Not)

instance Show1 (Not level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Not)

instance Eq child => Eq (Not level child) where
    (==) = eq1

instance Ord child => Ord (Not level child) where
    compare = compare1

instance Show child => Show (Not level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Not level child)

instance NFData child => NFData (Not level child)

instance Unparse child => Unparse (Not level child) where
    unparse Not { notSort, notChild } =
        "\\not"
        <> parameters [notSort]
        <> arguments [notChild]

    unparse2 Not { notChild } =
        Pretty.parens (Pretty.fillSep ["\\not", unparse2 notChild])
