{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Ceil
    ( Ceil (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
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

{-|'Ceil' corresponds to the @\ceil@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'ceilOperandSort' is the sort of the operand.

'ceilResultSort' is the sort of the result.

This represents the ⌈ceilPattern⌉ Matching Logic construct.
-}
data Ceil sort child = Ceil
    { ceilOperandSort :: !sort
    , ceilResultSort  :: !sort
    , ceilChild       :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Traversable, Show)

instance (Hashable sort, Hashable child) => Hashable (Ceil sort child)

instance (NFData sort, NFData child) => NFData (Ceil sort child)

instance SOP.Generic (Ceil sort child)

instance SOP.HasDatatypeInfo (Ceil sort child)

instance (Debug sort, Debug child) => Debug (Ceil sort child)

instance
    (Debug sort, Debug child, Diff sort, Diff child) => Diff (Ceil sort child)

instance Unparse child => Unparse (Ceil Sort child) where
    unparse Ceil { ceilOperandSort, ceilResultSort, ceilChild } =
        "\\ceil"
        <> parameters [ceilOperandSort, ceilResultSort]
        <> arguments [ceilChild]

    unparse2 Ceil { ceilChild } =
        Pretty.parens (Pretty.fillSep ["\\ceil", unparse2 ceilChild])

instance Ord variable => Synthetic (FreeVariables variable) (Ceil sort) where
    synthetic = ceilChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Ceil Sort) where
    synthetic Ceil { ceilOperandSort, ceilResultSort, ceilChild } =
        ceilResultSort
        & seq (matchSort ceilOperandSort ceilChild)
    {-# INLINE synthetic #-}
