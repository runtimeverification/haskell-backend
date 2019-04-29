{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Floor where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Unparser

{-|'Floor' corresponds to the @\floor@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'floorOperandSort' is the sort of the operand.

'floorResultSort' is the sort of the result.

-}
data Floor sort child = Floor
    { floorOperandSort :: !sort
    , floorResultSort  :: !sort
    , floorChild       :: child
    }
    deriving (Eq, Functor, Foldable, Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Floor
Deriving.deriveOrd1 ''Floor
Deriving.deriveShow1 ''Floor

instance (Hashable sort, Hashable child) => Hashable (Floor sort child)

instance (NFData sort, NFData child) => NFData (Floor sort child)

instance Unparse child => Unparse (Floor Sort child) where
    unparse Floor { floorOperandSort, floorResultSort, floorChild } =
        "\\floor"
        <> parameters [floorOperandSort, floorResultSort]
        <> arguments [floorChild]

    unparse2 Floor { floorChild } =
        Pretty.parens (Pretty.fillSep ["\\floor", unparse2 floorChild])
