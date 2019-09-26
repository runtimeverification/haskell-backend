{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.In
    ( In (..)
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

{-|'In' corresponds to the @\in@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'inOperandSort' is the sort of the operands.

'inResultSort' is the sort of the result.

-}
data In sort child = In
    { inOperandSort     :: !sort
    , inResultSort      :: !sort
    , inContainedChild  :: child
    , inContainingChild :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (In sort child)

instance (NFData sort, NFData child) => NFData (In sort child)

instance SOP.Generic (In sort child)

instance SOP.HasDatatypeInfo (In sort child)

instance (Debug sort, Debug child) => Debug (In sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (In sort child)

instance Unparse child => Unparse (In Sort child) where
    unparse
        In
            { inOperandSort
            , inResultSort
            , inContainedChild
            , inContainingChild
            }
      =
        "\\in"
        <> parameters [inOperandSort, inResultSort]
        <> arguments [inContainedChild, inContainingChild]

    unparse2
        In
            { inContainedChild
            , inContainingChild
            }
      = Pretty.parens (Pretty.fillSep
            [ "\\in"
            , unparse2 inContainedChild
            , unparse2 inContainingChild
            ])

instance Ord variable => Synthetic (FreeVariables variable) (In sort) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (In Sort) where
    synthetic in' =
        inResultSort
        & seq (matchSort inOperandSort inContainedChild)
        . seq (matchSort inOperandSort inContainingChild)
      where
        In { inResultSort, inOperandSort } = in'
        In { inContainedChild, inContainingChild } = in'
    {-# INLINE synthetic #-}
