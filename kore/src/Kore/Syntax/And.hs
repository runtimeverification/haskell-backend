{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.And (
    And (..),
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

{- |'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And sort child = And
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

instance Unparse child => Unparse (And Sort child) where
    unparse And{andSort, andFirst, andSecond} =
        "\\and"
            <> parameters [andSort]
            <> arguments [andFirst, andSecond]

    unparse2 And{andFirst, andSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\and"
                , unparse2 andFirst
                , unparse2 andSecond
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (And sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (And Sort) where
    synthetic And{andSort, andFirst, andSecond} =
        andSort
            & seq (matchSort andSort andFirst)
                . seq (matchSort andSort andSecond)
    {-# INLINE synthetic #-}
