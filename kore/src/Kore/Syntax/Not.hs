{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Not
    ( Not (..)
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
import Kore.TopBottom
import Kore.Unparser

{-|'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'notSort' is both the sort of the operand and the sort of the result.

-}
data Not sort child = Not
    { notSort  :: !sort
    , notChild :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (Not sort child)

instance (NFData sort, NFData child) => NFData (Not sort child)

instance SOP.Generic (Not sort child)

instance SOP.HasDatatypeInfo (Not sort child)

instance (Debug sort, Debug child) => Debug (Not sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (Not sort child)

instance Unparse child => Unparse (Not Sort child) where
    unparse Not { notSort, notChild } =
        "\\not"
        <> parameters [notSort]
        <> arguments [notChild]

    unparse2 Not { notChild } =
        Pretty.parens (Pretty.fillSep ["\\not", unparse2 notChild])

instance TopBottom child => TopBottom (Not sort child) where
    isTop = isBottom . notChild
    isBottom = isTop . notChild

instance Ord variable => Synthetic (FreeVariables variable) (Not child) where
    synthetic = notChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Not Sort) where
    synthetic Not { notSort, notChild } =
        notSort `matchSort` notChild
    {-# INLINE synthetic #-}
