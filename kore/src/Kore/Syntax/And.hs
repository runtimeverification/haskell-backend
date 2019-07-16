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
import qualified Data.Foldable as Foldable
import           Data.Function
import           Data.Functor.Classes
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeSetVariables
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
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
    deriving (Functor, Foldable, Traversable, GHC.Generic)

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

instance SOP.Generic (And sort child)

instance SOP.HasDatatypeInfo (And sort child)

instance (Debug sort, Debug child) => Debug (And sort child)

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

instance Ord variable => Synthetic (And sort) (FreeVariables variable) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Ord variable => Synthetic (And sort) (FreeSetVariables variable) where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic (And Sort) Sort where
    synthetic And { andSort, andFirst, andSecond } =
        andSort
        & seq (matchSort andSort andFirst)
        . seq (matchSort andSort andSecond)
    {-# INLINE synthetic #-}
