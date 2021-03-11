{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Mu
    ( Mu (..)
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.Variable
import Kore.Unparser
import qualified Pretty

{-|'Mu' corresponds to the @μ@ syntactic category from the
 Syntax of the MμL

The sort of the variable is the same as the sort of the result.

-}
data Mu variable child = Mu
    { muVariable :: !(SetVariable variable)
    , muChild    :: child
    }
    deriving (Eq, Ord, Show)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance
    (Unparse variable, Unparse child) => Unparse (Mu variable child)
  where
    unparse Mu { muVariable, muChild } =
        "\\mu"
        <> parameters ([] :: [Sort])
        <> arguments' [unparse muVariable, unparse muChild]

    unparse2 Mu { muVariable, muChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\mu"
            , unparse2SortedVariable muVariable
            , unparse2 muChild
            ])

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Mu variable)
  where
    synthetic Mu { muVariable, muChild } =
        bindVariable (inject muVariable) muChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (Mu variable) where
    synthetic Mu { muVariable, muChild } =
        muSort
        & seq (matchSort muSort muChild)
      where
        Variable { variableSort = muSort } = muVariable
    {-# INLINE synthetic #-}
