{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.And
    ( And (..)
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

{-|'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And sort child = And
    { andSort   :: !sort
    , andFirst  :: child
    , andSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

Deriving.deriveEq1 ''And
Deriving.deriveOrd1 ''And
Deriving.deriveShow1 ''And

instance (Eq sort, Eq child) => Eq (And sort child) where
    (==) = eq1

instance (Ord sort, Ord child) => Ord (And sort child) where
    compare = compare1

instance (Show sort, Show child) => Show (And sort child) where
    showsPrec = showsPrec1

instance (Hashable sort, Hashable child) => Hashable (And sort child)

instance (NFData sort, NFData child) => NFData (And sort child)

instance Unparse child => Unparse (And Sort child) where
    unparse And { andSort, andFirst, andSecond } =
        "\\and"
        <> parameters [andSort]
        <> arguments [andFirst, andSecond]

    unparse2 And { andFirst, andSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\and"
            , unparse2 andFirst
            , unparse2 andSecond
            ])
