{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Rewrites
    ( Rewrites (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

'rewritesSort' is both the sort of the operands and the sort of the result.

-}

data Rewrites sort child = Rewrites
    { rewritesSort   :: !sort
    , rewritesFirst  :: child
    , rewritesSecond :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (Rewrites sort child)

instance (NFData sort, NFData child) => NFData (Rewrites sort child)

instance SOP.Generic (Rewrites sort child)

instance SOP.HasDatatypeInfo (Rewrites sort child)

instance (Debug sort, Debug child) => Debug (Rewrites sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (Rewrites sort child)

instance Unparse child => Unparse (Rewrites Sort child) where
    unparse Rewrites { rewritesSort, rewritesFirst, rewritesSecond } =
        "\\rewrites"
        <> parameters [rewritesSort]
        <> arguments [rewritesFirst, rewritesSecond]

    unparse2 Rewrites { rewritesFirst, rewritesSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\rewrites"
            , unparse2 rewritesFirst
            , unparse2 rewritesSecond
            ])

instance Ord variable => Synthetic (FreeVariables variable) (Rewrites sort)
  where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Rewrites Sort) where
    synthetic Rewrites { rewritesSort, rewritesFirst, rewritesSecond } =
        rewritesSort
        & seq (matchSort rewritesSort rewritesFirst)
        . seq (matchSort rewritesSort rewritesSecond)
