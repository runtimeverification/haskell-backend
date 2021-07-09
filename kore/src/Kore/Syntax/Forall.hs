{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Forall (
    Forall (..),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.Variable
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- |'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'forallSort' is both the sort of the operands and the sort of the result.
-}
data Forall sort variable child = Forall
    { forallSort :: !sort
    , forallVariable :: !(ElementVariable variable)
    , forallChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance (Unparse variable, Unparse child) => Unparse (Forall Sort variable child) where
    unparse Forall{forallSort, forallVariable, forallChild} =
        "\\forall"
            <> parameters [forallSort]
            <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall{forallVariable, forallChild} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\forall"
                , unparse2SortedVariable forallVariable
                , unparse2 forallChild
                ]
            )

instance (Unparse variable, Unparse child) => Unparse (Forall () variable child) where
    unparse Forall{forallVariable, forallChild} =
        "\\forall"
            <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall{forallVariable, forallChild} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\forall"
                , unparse2SortedVariable forallVariable
                , unparse2 forallChild
                ]
            )

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Forall sort variable)
    where
    synthetic Forall{forallVariable, forallChild} =
        bindVariable (inject forallVariable) forallChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Forall Sort variable) where
    synthetic Forall{forallSort, forallChild} =
        forallSort `matchSort` forallChild
    {-# INLINE synthetic #-}
