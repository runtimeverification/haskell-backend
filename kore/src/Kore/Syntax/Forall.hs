{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Forall
    ( Forall (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Unparser

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'forallSort' is both the sort of the operands and the sort of the result.

-}
data Forall sort variable child = Forall
    { forallSort     :: !sort
    , forallVariable :: !variable
    , forallChild    :: child
    }
    deriving (Eq, Functor, Foldable, Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Forall
Deriving.deriveOrd1 ''Forall
Deriving.deriveShow1 ''Forall

instance
    (Hashable sort, Hashable variable, Hashable child) =>
    Hashable (Forall sort variable child)

instance
    (NFData sort, NFData variable, NFData child) =>
    NFData (Forall sort variable child)

instance
    (Unparse child, Unparse variable) =>
    Unparse (Forall Sort variable child)
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
