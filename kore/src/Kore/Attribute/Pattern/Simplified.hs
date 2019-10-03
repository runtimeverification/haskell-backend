{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Simplified
    ( Simplified (..)
    ) where

import Control.DeepSeq
import Data.Hashable
import Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Syntax
import Kore.Variables.UnifiedVariable

{- | A pattern is 'Simplified' if it has run through the simplifier.

All patterns are assumed un-simplified until marked otherwise.

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

instance {-# OVERLAPPABLE #-} Functor f => Synthetic Simplified f where
    synthetic = const (Simplified False)
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Bottom sort) where
    synthetic = const (Simplified True)
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Top sort) where
    synthetic = const (Simplified True)
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const StringLiteral) where
    synthetic = const (Simplified True)
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const CharLiteral) where
    synthetic = const (Simplified True)
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const (UnifiedVariable variable)) where
    synthetic = const (Simplified True)
    {-# INLINE synthetic #-}
