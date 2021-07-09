{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Rewrites (
    Rewrites (..),
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

{- |'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

'rewritesSort' is both the sort of the operands and the sort of the result.
-}
data Rewrites sort child = Rewrites
    { rewritesSort :: !sort
    , rewritesFirst :: !child
    , rewritesSecond :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (Rewrites Sort child) where
    unparse Rewrites{rewritesSort, rewritesFirst, rewritesSecond} =
        "\\rewrites"
            <> parameters [rewritesSort]
            <> arguments [rewritesFirst, rewritesSecond]

    unparse2 Rewrites{rewritesFirst, rewritesSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\rewrites"
                , unparse2 rewritesFirst
                , unparse2 rewritesSecond
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (Rewrites sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Rewrites Sort) where
    synthetic Rewrites{rewritesSort, rewritesFirst, rewritesSecond} =
        rewritesSort
            & seq (matchSort rewritesSort rewritesFirst)
                . seq (matchSort rewritesSort rewritesSecond)
