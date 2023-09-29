{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Syntax.And (
    And (..),
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
data And sort child = And
    { andSort :: !sort
    , andChildren :: ![child]
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance (Debug sort, Debug child) => Debug (And sort child)

instance
    ( Debug sort
    , Diff sort
    , Debug child
    , Diff child
    ) =>
    Diff (And sort child)

instance Unparse child => Unparse (And Sort child) where
    unparse And{andSort, andChildren} =
        "\\and"
            <> parameters [andSort]
            <> arguments andChildren

    unparse2 And{andChildren} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\and"
                , arguments2 andChildren
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (And sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (And Sort) where
    synthetic And{andSort, andChildren} =
        andSort
            & seq (map (sameSort andSort) andChildren)
    {-# INLINE synthetic #-}
