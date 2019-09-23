{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.And
    ( And (..)
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

{-|'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And sort child = And
    { andSort   :: !sort
    , andFirst  :: child
    , andSecond :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (And sort child)

instance (NFData sort, NFData child) => NFData (And sort child)

instance SOP.Generic (And sort child)

instance SOP.HasDatatypeInfo (And sort child)

instance (Debug sort, Debug child) => Debug (And sort child)

instance
    (Debug sort, Debug child, Diff sort, Diff child) => Diff (And sort child)

instance Unparse child => Unparse (And Sort child) where
    unparse And { andSort, andFirst, andSecond } =
        "\\and"
        <> parameters [andSort]
        <> arguments [andFirst, andSecond]

    unparse2 And { andFirst, andSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\and"
            , unparse2 andFirst
            , unparse2 andSecond
            ])

instance Ord variable => Synthetic (FreeVariables variable) (And sort) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (And Sort) where
    synthetic And { andSort, andFirst, andSecond } =
        andSort
        & seq (matchSort andSort andFirst)
        . seq (matchSort andSort andSecond)
    {-# INLINE synthetic #-}
