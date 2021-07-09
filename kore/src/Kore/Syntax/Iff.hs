{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Iff (
    Iff (..),
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

{- |'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'iffSort' is both the sort of the operands and the sort of the result.
-}
data Iff sort child = Iff
    { iffSort :: !sort
    , iffFirst :: !child
    , iffSecond :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (Iff Sort child) where
    unparse Iff{iffSort, iffFirst, iffSecond} =
        "\\iff"
            <> parameters [iffSort]
            <> arguments [iffFirst, iffSecond]

    unparse2 Iff{iffFirst, iffSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\iff"
                , unparse2 iffFirst
                , unparse2 iffSecond
                ]
            )

instance Unparse child => Unparse (Iff () child) where
    unparse Iff{iffFirst, iffSecond} =
        "\\iff"
            <> arguments [iffFirst, iffSecond]

    unparse2 Iff{iffFirst, iffSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\iff"
                , unparse2 iffFirst
                , unparse2 iffSecond
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (Iff sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Iff Sort) where
    synthetic Iff{iffSort, iffFirst, iffSecond} =
        iffSort
            & seq (matchSort iffSort iffFirst)
                . seq (matchSort iffSort iffSecond)
    {-# INLINE synthetic #-}
