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
import           Data.Functor.Classes
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

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
    deriving (Functor, Foldable, Traversable, Generic)

Deriving.deriveEq1 ''Or
Deriving.deriveOrd1 ''Or
Deriving.deriveShow1 ''Or

instance (Eq sort, Eq child) => Eq (Or sort child) where
    (==) = eq1

instance (Ord sort, Ord child) => Ord (Or sort child) where
    compare = compare1

instance (Show sort, Show child) => Show (Or sort child) where
    showsPrec = showsPrec1

instance (Hashable sort, Hashable child) => Hashable (Or sort child)

instance (NFData sort, NFData child) => NFData (Or sort child)

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
