{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Iff
    ( Iff (..)
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

{-|'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'iffSort' is both the sort of the operands and the sort of the result.

-}
data Iff sort child = Iff
    { iffSort   :: !sort
    , iffFirst  :: child
    , iffSecond :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (Iff sort child)

instance (NFData sort, NFData child) => NFData (Iff sort child)

instance SOP.Generic (Iff sort child)

instance SOP.HasDatatypeInfo (Iff sort child)

instance (Debug sort, Debug child) => Debug (Iff sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (Iff sort child)

instance Unparse child => Unparse (Iff Sort child) where
    unparse Iff { iffSort, iffFirst, iffSecond } =
        "\\iff"
        <> parameters [iffSort]
        <> arguments [iffFirst, iffSecond]

    unparse2 Iff { iffFirst, iffSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\iff"
            , unparse2 iffFirst
            , unparse2 iffSecond
            ])

instance Ord variable => Synthetic (FreeVariables variable) (Iff sort) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Iff Sort) where
    synthetic Iff { iffSort, iffFirst, iffSecond } =
        iffSort
        & seq (matchSort iffSort iffFirst)
        . seq (matchSort iffSort iffSecond)
    {-# INLINE synthetic #-}
