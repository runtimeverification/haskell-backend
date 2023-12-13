{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Syntax.Or (
    Or (..),
) where

import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified

{- | 'Or' corresponds to the @\\or@ branch of the @matching-logic-pattern@ syntactic category from <https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md#patterns kore-syntax.md#patterns>.

'orSort' is both the sort of the operands and the sort of the result.
-}
data Or sort child = Or
    { orSort :: !sort
    , orChildren :: ![child]
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance (Debug sort, Debug child) => Debug (Or sort child)

instance
    ( Debug sort
    , Diff sort
    , Debug child
    , Diff child
    ) =>
    Diff (Or sort child)

instance Pretty child => Pretty (Or Sort child) where
    pretty Or{orSort, orChildren} =
        "\\or"
            <> parameters [orSort]
            <> arguments' (pretty <$> orChildren)

instance Unparse child => Unparse (Or Sort child) where
    unparse Or{orSort, orChildren} =
        "\\or"
            <> parameters [orSort]
            <> arguments orChildren

    unparse2 Or{orChildren} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\or"
                , arguments2 orChildren
                ]
            )

instance Pretty child => Pretty (Or () child) where
    pretty Or{orChildren} =
        "\\or"
            <> arguments' (pretty <$> orChildren)
instance Unparse child => Unparse (Or () child) where
    unparse Or{orChildren} =
        "\\or"
            <> arguments orChildren

    unparse2 Or{orChildren} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\or"
                , arguments2 orChildren
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (Or sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Or Sort) where
    synthetic Or{orSort, orChildren} =
        orSort
            & seq (map (sameSort orSort) orChildren)
    {-# INLINE synthetic #-}
