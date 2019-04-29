{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Ceil where

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

{-|'Ceil' corresponds to the @\ceil@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'ceilOperandSort' is the sort of the operand.

'ceilResultSort' is the sort of the result.

This represents the ⌈ceilPattern⌉ Matching Logic construct.
-}
data Ceil level child = Ceil
    { ceilOperandSort :: !Sort
    , ceilResultSort  :: !Sort
    , ceilChild       :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Ceil level) where
    liftEq = $(makeLiftEq ''Ceil)

instance Ord1 (Ceil level) where
    liftCompare = $(makeLiftCompare ''Ceil)

instance Show1 (Ceil level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Ceil)

instance Eq child => Eq (Ceil level child) where
    (==) = eq1

instance Ord child => Ord (Ceil level child) where
    compare = compare1

instance Show child => Show (Ceil level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Ceil level child)

instance NFData child => NFData (Ceil level child)

instance Unparse child => Unparse (Ceil level child) where
    unparse Ceil { ceilOperandSort, ceilResultSort, ceilChild } =
        "\\ceil"
        <> parameters [ceilOperandSort, ceilResultSort]
        <> arguments [ceilChild]

    unparse2 Ceil { ceilChild } =
        Pretty.parens (Pretty.fillSep ["\\ceil", unparse2 ceilChild])
