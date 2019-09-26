{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Or
    ( Or (..)
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

{-|'Or' corresponds to the @\or@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'orSort' is both the sort of the operands and the sort of the result.

-}
data Or sort child = Or
    { orSort   :: !sort
    , orFirst  :: child
    , orSecond :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (Or sort child)

instance (NFData sort, NFData child) => NFData (Or sort child)

instance SOP.Generic (Or sort child)

instance SOP.HasDatatypeInfo (Or sort child)

instance (Debug sort, Debug child) => Debug (Or sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (Or sort child)

instance Unparse child => Unparse (Or Sort child) where
    unparse Or { orSort, orFirst, orSecond } =
        "\\or"
        <> parameters [orSort]
        <> arguments [orFirst, orSecond]

    unparse2 Or { orFirst, orSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\or"
            , unparse2 orFirst
            , unparse2 orSecond
            ])

instance Ord variable => Synthetic (FreeVariables variable) (Or sort) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Or Sort) where
    synthetic Or { orSort, orFirst, orSecond } =
        orSort
        & seq (matchSort orSort orFirst)
        . seq (matchSort orSort orSecond)
    {-# INLINE synthetic #-}
