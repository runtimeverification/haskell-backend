{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Mu
    ( Mu (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Sort
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
       ( SortedVariable, unparse2SortedVariable )
import Kore.Unparser

{-|'Mu' corresponds to the @μ@ syntactic category from the
 Syntax of the MμL

The sort of the variable is the same as the sort of the result.

-}
data Mu variable child = Mu
    { muVariable :: !(SetVariable variable)
    , muChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Mu
Deriving.deriveOrd1 ''Mu
Deriving.deriveShow1 ''Mu

instance
    (Hashable variable, Hashable child) =>
    Hashable (Mu variable child)

instance
    (NFData variable, NFData child) =>
    NFData (Mu variable child)

instance SOP.Generic (Mu variable child)

instance SOP.HasDatatypeInfo (Mu variable child)

instance
    (Debug variable, Debug child) =>
    Debug (Mu variable child)

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
            , unparse2SortedVariable (getVariable muVariable)
            , unparse2 muChild
            ])
