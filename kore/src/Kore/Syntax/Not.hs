{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Not (
    Not (..),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.TopBottom
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- |'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'notSort' is both the sort of the operand and the sort of the result.
-}
data Not sort child = Not
    { notSort :: !sort
    , notChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (Not Sort child) where
    unparse Not{notSort, notChild} =
        "\\not"
            <> parameters [notSort]
            <> arguments [notChild]

    unparse2 Not{notChild} =
        Pretty.parens (Pretty.fillSep ["\\not", unparse2 notChild])

instance Unparse child => Unparse (Not () child) where
    unparse Not{notChild} =
        "\\not"
            <> arguments [notChild]

    unparse2 Not{notChild} =
        Pretty.parens (Pretty.fillSep ["\\not", unparse2 notChild])

instance TopBottom child => TopBottom (Not sort child) where
    isTop = isBottom . notChild
    isBottom = isTop . notChild

instance Synthetic (FreeVariables variable) (Not child) where
    synthetic = notChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Not Sort) where
    synthetic Not{notSort, notChild} =
        notSort `matchSort` notChild
    {-# INLINE synthetic #-}
