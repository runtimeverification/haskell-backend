{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Implies (
    Implies (..),
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

{- |'Implies' corresponds to the @\implies@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'impliesSort' is both the sort of the operands and the sort of the result.
-}
data Implies sort child = Implies
    { impliesSort :: !sort
    , impliesFirst :: !child
    , impliesSecond :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (Implies Sort child) where
    unparse Implies{impliesSort, impliesFirst, impliesSecond} =
        "\\implies"
            <> parameters [impliesSort]
            <> arguments [impliesFirst, impliesSecond]

    unparse2 Implies{impliesFirst, impliesSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\implies"
                , unparse2 impliesFirst
                , unparse2 impliesSecond
                ]
            )

instance Unparse child => Unparse (Implies () child) where
    unparse Implies{impliesFirst, impliesSecond} =
        "\\implies"
            <> arguments [impliesFirst, impliesSecond]

    unparse2 Implies{impliesFirst, impliesSecond} =
        Pretty.parens
            ( Pretty.fillSep
                [ "\\implies"
                , unparse2 impliesFirst
                , unparse2 impliesSecond
                ]
            )

instance Ord variable => Synthetic (FreeVariables variable) (Implies sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Implies Sort) where
    synthetic Implies{impliesSort, impliesFirst, impliesSecond} =
        impliesSort
            & seq (matchSort impliesSort impliesFirst)
                . seq (matchSort impliesSort impliesSecond)
    {-# INLINE synthetic #-}
