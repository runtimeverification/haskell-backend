{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Or
    ( Or (..)
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
import Kore.Unparser

{-|'Or' corresponds to the @\or@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'orSort' is both the sort of the operands and the sort of the result.

-}
data Or sort child = Or
    { orSort   :: !sort
    , orFirst  :: child
    , orSecond :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Or
Deriving.deriveOrd1 ''Or
Deriving.deriveShow1 ''Or

instance (Hashable sort, Hashable child) => Hashable (Or sort child)

instance (NFData sort, NFData child) => NFData (Or sort child)

instance SOP.Generic (Or sort child)

instance SOP.HasDatatypeInfo (Or sort child)

instance (Debug sort, Debug child) => Debug (Or sort child)

instance Unparse child => Unparse (Or Sort child) where
    unparse Or { orSort, orFirst, orSecond } =
        "\\or"
        <> parameters [orSort]
        <> arguments [orFirst, orSecond]

    unparse2 Or { orFirst, orSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\or"
            , unparse2 orFirst
            , unparse2 orSecond
            ])
