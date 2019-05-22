{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Nu
    ( Nu (..)
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

{-|'Nu' corresponds to the @ν@ syntactic category from the
 Syntax of the MμL

The sort of the variable is the same as the sort of the result.

-}
data Nu variable child = Nu
    { nuVariable :: !(SetVariable variable)
    , nuChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Nu
Deriving.deriveOrd1 ''Nu
Deriving.deriveShow1 ''Nu

instance
    (Hashable variable, Hashable child) =>
    Hashable (Nu variable child)

instance
    (NFData variable, NFData child) =>
    NFData (Nu variable child)

instance SOP.Generic (Nu variable child)

instance SOP.HasDatatypeInfo (Nu variable child)

instance
    (Debug variable, Debug child) =>
    Debug (Nu variable child)

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
            , unparse2SortedVariable (getVariable nuVariable)
            , unparse2 nuChild
            ])
