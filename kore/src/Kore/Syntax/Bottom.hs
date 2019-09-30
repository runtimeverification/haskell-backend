{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Bottom
    ( Bottom (..)
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

{- | 'Bottom' corresponds to the @\bottom@ branches of the @pattern@ syntactic
category from the Semantics of K, Section 9.1.4 (Patterns).

'bottomSort' is the sort of the result.

 -}
newtype Bottom sort child = Bottom { bottomSort :: sort }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Traversable, Show)

instance Hashable sort => Hashable (Bottom sort child)

instance NFData sort => NFData (Bottom sort child)

instance SOP.Generic (Bottom sort child)

instance SOP.HasDatatypeInfo (Bottom sort child)

instance Debug sort => Debug (Bottom sort child)

instance (Debug sort, Diff sort) => Diff (Bottom sort child)

instance Unparse (Bottom Sort child) where
    unparse Bottom { bottomSort } =
        "\\bottom" <> parameters [bottomSort] <> noArguments
    unparse2 _ = "\\bottom"

instance Ord variable => Synthetic (FreeVariables variable) (Bottom sort) where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance Synthetic Sort (Bottom Sort) where
    synthetic = bottomSort
    {-# INLINE synthetic #-}
