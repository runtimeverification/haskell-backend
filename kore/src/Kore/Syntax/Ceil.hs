{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Ceil (
    Ceil (..),
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

{- |'Ceil' corresponds to the @\ceil@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'ceilOperandSort' is the sort of the operand.

'ceilResultSort' is the sort of the result.

This represents the ⌈ceilPattern⌉ Matching Logic construct.
-}
data Ceil sort child = Ceil
    { ceilOperandSort :: !sort
    , ceilResultSort :: !sort
    , ceilChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (Ceil Sort child) where
    unparse Ceil{ceilOperandSort, ceilResultSort, ceilChild} =
        "\\ceil"
            <> parameters [ceilOperandSort, ceilResultSort]
            <> arguments [ceilChild]

    unparse2 Ceil{ceilChild} =
        Pretty.parens (Pretty.fillSep ["\\ceil", unparse2 ceilChild])

instance Unparse child => Unparse (Ceil () child) where
    unparse Ceil{ceilChild} =
        "\\ceil"
            <> arguments [ceilChild]

    unparse2 Ceil{ceilChild} =
        Pretty.parens (Pretty.fillSep ["\\ceil", unparse2 ceilChild])

instance Synthetic (FreeVariables variable) (Ceil sort) where
    synthetic = ceilChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Ceil Sort) where
    synthetic Ceil{ceilOperandSort, ceilResultSort, ceilChild} =
        ceilResultSort
            & seq (matchSort ceilOperandSort ceilChild)
    {-# INLINE synthetic #-}
