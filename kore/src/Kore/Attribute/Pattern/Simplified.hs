{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Simplified
    ( Simplified (..)
    , alwaysSimplified
    , notSimplified
    ) where

import Control.DeepSeq
import Data.Hashable
import Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Builtin
import Kore.Syntax
import Kore.Variables.UnifiedVariable

{- | A pattern is 'Simplified' if it has run through the simplifier.

The simplifier runs until we do not know how to simplify a pattern any more. A
pattern 'isSimplified' if re-applying the simplifier would return the same
pattern.

All patterns are assumed un-simplified until marked otherwise, so that
'isSimplified' is reset by any substitution under the pattern.

 -}
newtype Simplified = Simplified { isSimplified :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Simplified

instance SOP.HasDatatypeInfo Simplified

instance Debug Simplified

instance Diff Simplified where
    diffPrec = diffPrecIgnore

instance NFData Simplified

instance Hashable Simplified

alwaysSimplified :: a -> Simplified
alwaysSimplified = const (Simplified True)
{-# INLINE alwaysSimplified #-}

notSimplified :: a -> Simplified
notSimplified = const (Simplified False)
{-# INLINE notSimplified #-}

instance Synthetic Simplified (Bottom sort) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Top sort) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const StringLiteral) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const (UnifiedVariable variable)) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Exists sort variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Forall sort variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (And sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Or sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Not sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Application head) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Ceil sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Floor sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (DomainValue sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Equals sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (In sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Implies sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Iff sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Mu variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Nu variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Next sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Rewrites sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Builtin sort) where
    synthetic (BuiltinInt    _) = Simplified True
    synthetic (BuiltinBool   _) = Simplified True
    synthetic (BuiltinString _) = Simplified True
    synthetic (BuiltinMap    _) = Simplified False
    synthetic (BuiltinList   _) = Simplified False
    synthetic (BuiltinSet    _) = Simplified False
    {-# INLINE synthetic #-}

instance Synthetic Simplified Inhabitant where
    synthetic = notSimplified
    {-# INLINE synthetic #-}
