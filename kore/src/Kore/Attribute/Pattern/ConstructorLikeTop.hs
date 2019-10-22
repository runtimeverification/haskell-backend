{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.ConstructorLikeTop
    ( ConstructorLikeTop (..)
    ) where

import Control.DeepSeq
import Data.Functor.Const
import Data.Hashable
import Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Builtin
import qualified Kore.Internal.Alias as Internal
import qualified Kore.Internal.Symbol as Internal
import Kore.Syntax
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

{- | A pattern is 'ConstructorLikeTop' if it is one of the following:

- A 'StringLiteral'
- A 'Domain Value'
- A 'Builtin'
- An 'Application' whose head is a constructor symbol
 -}
newtype ConstructorLikeTop = ConstructorLikeTop { isConstructorLikeTop :: Bool }
    deriving (Eq, GHC.Generic, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic ConstructorLikeTop

instance SOP.HasDatatypeInfo ConstructorLikeTop

instance Debug ConstructorLikeTop

instance Diff ConstructorLikeTop

instance NFData ConstructorLikeTop

instance Hashable ConstructorLikeTop

instance Synthetic ConstructorLikeTop (And sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Bottom sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

-- | An 'Application' is 'ConstructorLikeTop' if its symbol is a constructor
instance Synthetic ConstructorLikeTop (Application Internal.Symbol) where
    synthetic application = ConstructorLikeTop $ Internal.isConstructor symbol
      where
        symbol = applicationSymbolOrAlias application
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop
    (Application (Internal.Alias patternType))
  where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Ceil sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

-- | A 'DomainValue' pattern is 'ConstructorLikeTop'
instance Synthetic ConstructorLikeTop (DomainValue sort) where
    synthetic =  const (ConstructorLikeTop True)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Equals sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Exists sort variable) where
    synthetic = const (ConstructorLikeTop False)

instance Synthetic ConstructorLikeTop (Floor sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Forall sort variable) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Iff sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Implies sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (In sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Mu sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Next sort) where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Not sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Nu sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Or sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Rewrites sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is 'ConstructorLikeTop'
instance Synthetic ConstructorLikeTop (Builtin key) where
    synthetic = const (ConstructorLikeTop True)
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLikeTop (Top sort) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'ConstructorLikeTop'.
instance Synthetic ConstructorLikeTop (Const StringLiteral) where
    synthetic = const (ConstructorLikeTop True)
    {-# INLINE synthetic #-}

-- | An 'Inhabitant' pattern is never 'ConstructorLikeTop'.
instance Synthetic ConstructorLikeTop Inhabitant where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}

-- | A 'Variable' pattern is never 'ConstructorLikeTop'.
instance Synthetic ConstructorLikeTop (Const (UnifiedVariable variable)) where
    synthetic = const (ConstructorLikeTop False)
    {-# INLINE synthetic #-}
