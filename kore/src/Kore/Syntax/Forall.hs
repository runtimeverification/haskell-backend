{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Forall
    ( Forall (..)
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
import Kore.Syntax.ElementVariable
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.UnifiedVariable

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'forallSort' is both the sort of the operands and the sort of the result.

-}
data Forall sort variable child = Forall
    { forallSort     :: !sort
    , forallVariable :: !(ElementVariable variable)
    , forallChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance
    (Hashable sort, Hashable variable, Hashable child) =>
    Hashable (Forall sort variable child)

instance
    (NFData sort, NFData variable, NFData child) =>
    NFData (Forall sort variable child)

instance SOP.Generic (Forall sort variable child)

instance SOP.HasDatatypeInfo (Forall sort variable child)

instance
    (Debug sort, Debug variable, Debug child) =>
    Debug (Forall sort variable child)

instance
    ( Debug sort, Debug variable, Debug child
    , Diff sort, Diff variable, Diff child
    )
    => Diff (Forall sort variable child)

instance
    (SortedVariable variable, Unparse variable, Unparse child) =>
    Unparse (Forall Sort variable child)
  where
    unparse Forall { forallSort, forallVariable, forallChild } =
        "\\forall"
        <> parameters [forallSort]
        <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall { forallVariable, forallChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\forall"
            , unparse2SortedVariable (getElementVariable forallVariable)
            , unparse2 forallChild
            ])

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Forall sort variable)
  where
    synthetic Forall { forallVariable, forallChild } =
        bindVariable (ElemVar forallVariable) forallChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Forall Sort variable) where
    synthetic Forall { forallSort, forallChild } =
        forallSort `matchSort` forallChild
    {-# INLINE synthetic #-}
