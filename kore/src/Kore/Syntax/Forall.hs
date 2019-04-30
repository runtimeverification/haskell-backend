{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Forall where

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

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'forallSort' is both the sort of the operands and the sort of the result.

-}
data Forall level variable child = Forall
    { forallSort     :: !Sort
    , forallVariable :: !variable
    , forallChild    :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq variable => Eq1 (Forall lvl variable) where
    liftEq = $(makeLiftEq ''Forall)

instance Ord variable => Ord1 (Forall lvl variable) where
    liftCompare = $(makeLiftCompare ''Forall)

instance Show variable => Show1 (Forall lvl variable) where
    liftShowsPrec = $(makeLiftShowsPrec ''Forall)

instance (Eq child, Eq variable) => Eq (Forall lvl variable child) where
    (==) = eq1

instance (Ord child, Ord variable) => Ord (Forall lvl variable child) where
    compare = compare1

instance (Show child, Show variable) => Show (Forall lvl variable child) where
    showsPrec = showsPrec1

instance (Hashable child, Hashable variable) => Hashable (Forall lvl variable child)

instance (NFData child, NFData variable) => NFData (Forall lvl variable child)

instance
    ( Unparse child
    , Unparse variable
    ) =>
    Unparse (Forall level variable child)
  where
    unparse Forall { forallSort, forallVariable, forallChild } =
        "\\forall"
        <> parameters [forallSort]
        <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall { forallVariable, forallChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\forall"
            , unparse2BindingVariables forallVariable
            , unparse2 forallChild
            ])
