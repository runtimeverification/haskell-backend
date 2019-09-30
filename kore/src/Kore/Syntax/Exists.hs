{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Exists
    ( Exists (..)
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

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'existsSort' is both the sort of the operands and the sort of the result.

-}
data Exists sort variable child = Exists
    { existsSort     :: !sort
    , existsVariable :: !(ElementVariable variable)
    , existsChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance
    (Hashable sort, Hashable variable, Hashable child) =>
    Hashable (Exists sort variable child)

instance
    (NFData sort, NFData variable, NFData child) =>
    NFData (Exists sort variable child)

instance SOP.Generic (Exists sort variable child)

instance SOP.HasDatatypeInfo (Exists sort variable child)

instance
    (Debug sort, Debug variable, Debug child) =>
    Debug (Exists sort variable child)

instance
    ( Debug sort, Debug variable, Debug child
    , Diff sort, Diff variable, Diff child
    )
    => Diff (Exists sort variable child)

instance
    (SortedVariable variable, Unparse variable, Unparse child) =>
    Unparse (Exists Sort variable child)
  where
    unparse Exists { existsSort, existsVariable, existsChild } =
        "\\exists"
        <> parameters [existsSort]
        <> arguments' [unparse existsVariable, unparse existsChild]

    unparse2 Exists { existsVariable, existsChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\exists"
            , unparse2SortedVariable (getElementVariable existsVariable)
            , unparse2 existsChild
            ])

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Exists sort variable)
  where
    synthetic Exists { existsVariable, existsChild } =
        bindVariable (ElemVar existsVariable) existsChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Exists Sort variable) where
    synthetic Exists { existsSort, existsChild } =
        existsSort `matchSort` existsChild
    {-# INLINE synthetic #-}
