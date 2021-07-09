{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Attribute.Pattern.Functional (
    Functional (..),
    alwaysFunctional,
) where

import Data.Functor.Const
import Data.Monoid
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Synthetic
import Kore.Debug
import qualified Kore.Internal.Alias as Internal
import Kore.Internal.Inj (
    Inj,
 )
import qualified Kore.Internal.Inj as Inj
import qualified Kore.Internal.Symbol as Internal
import Kore.Syntax
import Prelude.Kore

-- | A pattern is 'Functional' if it matches exactly one element.
newtype Functional = Functional {isFunctional :: Bool}
    deriving stock (Eq, GHC.Generic, Ord, Show)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via All

alwaysFunctional :: a -> Functional
alwaysFunctional = const (Functional True)
{-# INLINE alwaysFunctional #-}

instance Synthetic Functional (And sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Bottom sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

{- | An 'Application' pattern is 'Functional' if its symbol is functional and
 its arguments are 'Functional'.
-}
instance Synthetic Functional (Application Internal.Symbol) where
    synthetic application =
        functionalSymbol <> fold children
      where
        functionalSymbol = Functional (Internal.isFunctional symbol)
        children = applicationChildren application
        symbol = applicationSymbolOrAlias application

instance Synthetic Functional (Application (Internal.Alias patternType)) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Ceil sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | A 'DomainValue' pattern is 'Functional' if its argument is 'Functional'.
instance Synthetic Functional (DomainValue sort) where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic Functional (Equals sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Exists sort variable) where
    synthetic = const (Functional False)

instance Synthetic Functional (Floor sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Forall sort variable) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Iff sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Implies sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (In sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Mu sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Next sort) where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic Functional (Not sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Nu sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Or sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Rewrites sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Top sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Const (SomeVariable variable)) where
    synthetic (Const unifiedVariable) =
        Functional (isElementVariable unifiedVariable)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'Functional'.
instance Synthetic Functional (Const StringLiteral) where
    synthetic = const (Functional True)
    {-# INLINE synthetic #-}

-- | An 'Inhabitant' pattern is never 'Functional'.
instance Synthetic Functional Inhabitant where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Const Sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional Inj where
    synthetic = synthetic . Inj.toApplication
    {-# INLINE synthetic #-}
