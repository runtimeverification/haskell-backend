{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Builtin.AssocComm.AssocComm (
    UnitSymbol (..),
    ConcatSymbol (..),
    ConcreteElements (..),
    VariableElements (..),
    Opaque (..),
) where

import Kore.Internal.Symbol (
    Symbol,
 )
import Kore.Internal.TermLike (
    Concrete,
    TermLike,
 )
import Prelude.Kore

-- | Particularizes @Domain.NormalizedAc@ to the most common types.
type TermNormalizedAc normalized variable =
    normalized (TermLike Concrete) (TermLike variable)

{- | A normalized representation of an associative-commutative structure that
also allows bottom values.
-}
data NormalizedOrBottom collection variable
    = Normalized (TermNormalizedAc collection variable)
    | Bottom

deriving stock instance
    Eq (TermNormalizedAc collection variable) =>
    Eq (NormalizedOrBottom collection variable)

deriving stock instance
    Ord (TermNormalizedAc collection variable) =>
    Ord (NormalizedOrBottom collection variable)

deriving stock instance
    Show (TermNormalizedAc collection variable) =>
    Show (NormalizedOrBottom collection variable)

-- | Wrapper for giving names to arguments.
newtype UnitSymbol = UnitSymbol {getUnitSymbol :: Symbol}

-- | Wrapper for giving names to arguments.
newtype ConcatSymbol = ConcatSymbol {getConcatSymbol :: Symbol}

-- | Wrapper for giving names to arguments.
newtype ConcreteElements variable = ConcreteElements {getConcreteElements :: [TermLike variable]}

-- | Wrapper for giving names to arguments.
newtype VariableElements variable = VariableElements {getVariableElements :: [TermLike variable]}

-- | Wrapper for giving names to arguments.
newtype Opaque variable = Opaque {getOpaque :: [TermLike variable]}
