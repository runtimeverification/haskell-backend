{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Total
    ( Total (..)
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

newtype Total = Total { isTotal :: Bool }
    deriving (Eq, GHC.Generic, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Total

instance SOP.HasDatatypeInfo Total

instance Debug Total

instance NFData Total

instance Hashable Total

instance Synthetic (And sort) Total where
    -- TODO (thomas.tuegel):
    -- synthetic = Foldable.fold
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Bottom sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Application Internal.Symbol) Total where
    synthetic application =
        functionSymbol <> Foldable.fold children
      where
        functionSymbol = Total (Internal.isTotal symbol)
        children = applicationChildren application
        symbol = applicationSymbolOrAlias application

instance Synthetic (Application Internal.Alias) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Ceil sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (DomainValue sort) Total where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic (Equals sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Exists sort variable) Total where
    synthetic = const (Total False)

instance Synthetic (Floor sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Forall sort variable) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Iff sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Implies sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (In sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Mu sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Next sort) Total where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic (Not sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Nu sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Or sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Rewrites sort) Total where
    synthetic = const (Total False)
    {-# INLINE synthetic #-}

instance Synthetic (Builtin key) Total where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic (Top sort) Total where
    synthetic = const (Total True)
    {-# INLINE synthetic #-}

instance Synthetic (Const StringLiteral) Total where
    synthetic = const (Total True)
    {-# INLINE synthetic #-}

instance Synthetic (Const CharLiteral) Total where
    synthetic = const (Total True)
    {-# INLINE synthetic #-}

instance Synthetic (Const Variable) Total where
    synthetic = const (Total True)
    {-# INLINE synthetic #-}
