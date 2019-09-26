{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Next
    ( Next (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

'nextSort' is both the sort of the operand and the sort of the result.

-}
data Next sort child = Next
    { nextSort  :: !sort
    , nextChild :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (Next sort child)

instance (NFData sort, NFData child) => NFData (Next sort child)

instance SOP.Generic (Next sort child)

instance SOP.HasDatatypeInfo (Next sort child)

instance (Debug sort, Debug child) => Debug (Next sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (Next sort child)

instance Unparse child => Unparse (Next Sort child) where
    unparse Next { nextSort, nextChild } =
        "\\next"
        <> parameters [nextSort]
        <> arguments [nextChild]

    unparse2 Next { nextChild } =
        Pretty.parens (Pretty.fillSep ["\\next", unparse2 nextChild])

instance Ord variable => Synthetic (FreeVariables variable) (Next sort) where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Next Sort) where
    synthetic Next { nextSort, nextChild } =
        nextSort `matchSort` nextChild
    {-# INLINE synthetic #-}
