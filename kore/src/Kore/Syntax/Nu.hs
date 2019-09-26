{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Nu
    ( Nu (..)
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
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.UnifiedVariable

{-|'Nu' corresponds to the @ν@ syntactic category from the
 Syntax of the MμL

The sort of the variable is the same as the sort of the result.

-}
data Nu variable child = Nu
    { nuVariable :: !(SetVariable variable)
    , nuChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable variable, Hashable child) => Hashable (Nu variable child)

instance (NFData variable, NFData child) => NFData (Nu variable child)

instance SOP.Generic (Nu variable child)

instance SOP.HasDatatypeInfo (Nu variable child)

instance (Debug variable, Debug child) => Debug (Nu variable child)

instance
    ( Debug variable, Debug child, Diff variable, Diff child )
    => Diff (Nu variable child)

instance
    (SortedVariable variable, Unparse variable, Unparse child) =>
    Unparse (Nu variable child)
  where
    unparse Nu {nuVariable, nuChild } =
        "\\nu"
        <> parameters ([] :: [Sort])
        <> arguments' [unparse nuVariable, unparse nuChild]

    unparse2 Nu {nuVariable, nuChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\nu"
            , unparse2SortedVariable (getSetVariable nuVariable)
            , unparse2 nuChild
            ])

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Nu variable)
  where
    synthetic Nu { nuVariable, nuChild } =
        bindVariable (SetVar nuVariable) nuChild
    {-# INLINE synthetic #-}

instance SortedVariable variable => Synthetic Sort (Nu variable) where
    synthetic Nu { nuVariable, nuChild } =
        nuSort
        & seq (matchSort nuSort nuChild)
      where
        nuSort = sortedVariableSort (getSetVariable nuVariable)
    {-# INLINE synthetic #-}
