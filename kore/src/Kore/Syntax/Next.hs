{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Next (
    Next (..),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- |'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

'nextSort' is both the sort of the operand and the sort of the result.
-}
data Next sort child = Next
    { nextSort :: !sort
    , nextChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (Next Sort child) where
    unparse Next{nextSort, nextChild} =
        "\\next"
            <> parameters [nextSort]
            <> arguments [nextChild]

    unparse2 Next{nextChild} =
        Pretty.parens (Pretty.fillSep ["\\next", unparse2 nextChild])

instance Synthetic (FreeVariables variable) (Next sort) where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Next Sort) where
    synthetic Next{nextSort, nextChild} =
        nextSort `matchSort` nextChild
    {-# INLINE synthetic #-}
