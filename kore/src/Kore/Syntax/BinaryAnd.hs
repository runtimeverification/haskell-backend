{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Syntax.BinaryAnd (
    BinaryAnd (..),
) where

import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Prelude.Kore
import Pretty qualified

{- | 'And' corresponds to the @\\and@ branch of the @matching-logic-pattern@ syntactic category from <https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md#patterns kore-syntax.md#patterns>.

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data BinaryAnd sort child = BinaryAnd
    { andSort :: !sort
    , andFirst :: !child
    , andSecond :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (BinaryAnd Sort child) where
    unparse BinaryAnd{andSort, andFirst, andSecond} =
        "\\and"
            <> parameters [andSort]
            <> arguments [andFirst, andSecond]

    unparse2 BinaryAnd{andFirst, andSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\and"
                , unparse2 andFirst
                , unparse2 andSecond
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (BinaryAnd sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (BinaryAnd Sort) where
    synthetic BinaryAnd{andSort, andFirst, andSecond} =
        andSort
            & seq (sameSort andSort andFirst)
            . seq (sameSort andSort andSecond)
    {-# INLINE synthetic #-}
