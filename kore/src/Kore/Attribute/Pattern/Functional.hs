{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Functional
    ( Functional (..)
    ) where

import           Control.DeepSeq
import qualified Data.Foldable as Foldable
import           Data.Functor.Const
import           Data.Hashable
import           Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import           Kore.Attribute.Synthetic
import           Kore.Debug
import           Kore.Domain.Builtin
import qualified Kore.Internal.Alias as Internal
import qualified Kore.Internal.Symbol as Internal
import           Kore.Syntax

{- | A pattern is 'Functional' if it matches exactly one element.
 -}
newtype Functional = Functional { isFunctional :: Bool }
    deriving (Eq, GHC.Generic, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Functional

instance SOP.HasDatatypeInfo Functional

instance Debug Functional

instance NFData Functional

instance Hashable Functional

instance Synthetic (And sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Bottom sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | An 'Application' pattern is 'Functional' if its symbol is functional and
-- its arguments are 'Functional'.
instance Synthetic (Application Internal.Symbol) Functional where
    synthetic application =
        functionalSymbol <> Foldable.fold children
      where
        functionalSymbol = Functional (Internal.isFunctional symbol)
        children = applicationChildren application
        symbol = applicationSymbolOrAlias application

instance Synthetic (Application Internal.Alias) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Ceil sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | A 'DomainValue' pattern is 'Functional' if its argument is 'Functional'.
instance Synthetic (DomainValue sort) Functional where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic (Equals sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Exists sort variable) Functional where
    synthetic = const (Functional False)

instance Synthetic (Floor sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Forall sort variable) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Iff sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Implies sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (In sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Mu sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Next sort) Functional where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic (Not sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Nu sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Or sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic (Rewrites sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is 'Functional' if its subterms are 'Functional'.
instance Synthetic (Builtin key) Functional where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic (Top sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | A 'Variable' pattern is always 'Functional'.
instance Synthetic (Const Variable) Functional where
    synthetic = const (Functional True)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'Functional'.
instance Synthetic (Const StringLiteral) Functional where
    synthetic = const (Functional True)
    {-# INLINE synthetic #-}

-- | A 'CharLiteral' pattern is always 'Functional'.
instance Synthetic (Const CharLiteral) Functional where
    synthetic = const (Functional True)
    {-# INLINE synthetic #-}

instance Synthetic (Const Sort) Functional where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}
