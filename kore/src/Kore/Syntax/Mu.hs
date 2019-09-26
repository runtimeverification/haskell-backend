{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Mu
    ( Mu (..)
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

{-|'Mu' corresponds to the @μ@ syntactic category from the
 Syntax of the MμL

The sort of the variable is the same as the sort of the result.

-}
data Mu variable child = Mu
    { muVariable :: !(SetVariable variable)
    , muChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

instance (Hashable variable, Hashable child) => Hashable (Mu variable child)

instance (NFData variable, NFData child) => NFData (Mu variable child)

instance SOP.Generic (Mu variable child)

instance SOP.HasDatatypeInfo (Mu variable child)

instance (Debug variable, Debug child) => Debug (Mu variable child)

instance
    ( Debug variable, Debug child, Diff variable, Diff child )
    => Diff (Mu variable child)

instance
    (SortedVariable variable, Unparse variable, Unparse child) =>
    Unparse (Mu variable child)
  where
    unparse Mu { muVariable, muChild } =
        "\\mu"
        <> parameters ([] :: [Sort])
        <> arguments' [unparse muVariable, unparse muChild]

    unparse2 Mu { muVariable, muChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\mu"
            , unparse2SortedVariable (getSetVariable muVariable)
            , unparse2 muChild
            ])

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Mu variable)
  where
    synthetic Mu { muVariable, muChild } =
        bindVariable (SetVar muVariable) muChild
    {-# INLINE synthetic #-}

instance SortedVariable variable => Synthetic Sort (Mu variable) where
    synthetic Mu { muVariable, muChild } =
        muSort
        & seq (matchSort muSort muChild)
      where
        muSort = sortedVariableSort (getSetVariable muVariable)
    {-# INLINE synthetic #-}
