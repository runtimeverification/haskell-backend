{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Exists where

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

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'existsSort' is both the sort of the operands and the sort of the result.

This represents the '∃existsVariable(existsChild)' Matching Logic construct.
-}
data Exists level variable child = Exists
    { existsSort     :: !Sort
    , existsVariable :: !variable
    , existsChild    :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq variable => Eq1 (Exists lvl variable) where
    liftEq = $(makeLiftEq ''Exists)

instance Ord variable => Ord1 (Exists lvl variable) where
    liftCompare = $(makeLiftCompare ''Exists)

instance Show variable => Show1 (Exists lvl variable) where
    liftShowsPrec = $(makeLiftShowsPrec ''Exists)

instance (Eq child, Eq variable) => Eq (Exists lvl variable child) where
    (==) = eq1

instance (Ord child, Ord variable) => Ord (Exists lvl variable child) where
    compare = compare1

instance (Show child, Show variable) => Show (Exists lvl variable child) where
    showsPrec = showsPrec1

instance (Hashable child, Hashable variable) => Hashable (Exists lvl variable child)

instance (NFData child, NFData variable) => NFData (Exists lvl variable child)

instance
    ( Unparse child
    , Unparse variable
    ) =>
    Unparse (Exists level variable child)
  where
    unparse Exists { existsSort, existsVariable, existsChild } =
        "\\exists"
        <> parameters [existsSort]
        <> arguments' [unparse existsVariable, unparse existsChild]

    unparse2 Exists { existsVariable, existsChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\exists"
            , unparse2BindingVariables existsVariable
            , unparse2 existsChild
            ])
