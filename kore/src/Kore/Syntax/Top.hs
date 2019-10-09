{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Top
    ( Top (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).


'topSort' is the sort of the result.
-}
newtype Top sort child = Top { topSort :: sort }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance Hashable sort => Hashable (Top sort child)

instance NFData sort => NFData (Top sort child)

instance SOP.Generic (Top sort child)

instance SOP.HasDatatypeInfo (Top sort child)

instance Debug sort => Debug (Top sort child)

instance (Debug sort, Diff sort) => Diff (Top sort child)

instance Unparse (Top Sort child) where
    unparse Top { topSort } = "\\top" <> parameters [topSort] <> noArguments

    unparse2 _ = "\\top"

instance Ord variable => Synthetic (FreeVariables variable) (Top sort) where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance Synthetic Sort (Top Sort) where
    synthetic = topSort
    {-# INLINE synthetic #-}
