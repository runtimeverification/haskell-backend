{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Syntax.BinaryOr (
    BinaryOr (..),
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
data BinaryOr sort child = BinaryOr
    { orSort :: !sort
    , orFirst :: !child
    , orSecond :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty child => Pretty (BinaryOr Sort child) where
    pretty BinaryOr{orSort, orFirst, orSecond} =
        "\\or"
            <> parameters [orSort]
            <> arguments' (pretty <$> [orFirst, orSecond])

instance Unparse child => Unparse (BinaryOr Sort child) where
    unparse BinaryOr{orSort, orFirst, orSecond} =
        "\\or"
            <> parameters [orSort]
            <> arguments [orFirst, orSecond]

    unparse2 BinaryOr{orFirst, orSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\or"
                , unparse2 orFirst
                , unparse2 orSecond
                ]
            )

instance Pretty child => Pretty (BinaryOr () child) where
    pretty BinaryOr{orFirst, orSecond} =
        "\\or"
            <> arguments' (pretty <$> [orFirst, orSecond])
instance Unparse child => Unparse (BinaryOr () child) where
    unparse BinaryOr{orFirst, orSecond} =
        "\\or"
            <> arguments [orFirst, orSecond]

    unparse2 BinaryOr{orFirst, orSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\or"
                , unparse2 orFirst
                , unparse2 orSecond
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (BinaryOr sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (BinaryOr Sort) where
    synthetic BinaryOr{orSort, orFirst, orSecond} =
        orSort
            & seq (sameSort orSort orFirst)
                . seq (sameSort orSort orSecond)
    {-# INLINE synthetic #-}
