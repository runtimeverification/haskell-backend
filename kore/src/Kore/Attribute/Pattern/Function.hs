{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Function
    ( Function (..)
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
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )

{- | A pattern is 'Function' if it matches zero or one elements.
 -}
newtype Function = Function { isFunction :: Bool }
    deriving (Eq, GHC.Generic, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Function

instance SOP.HasDatatypeInfo Function

instance Debug Function

instance NFData Function

instance Hashable Function

instance Synthetic (And sort) Function where
    -- TODO (thomas.tuegel):
    -- synthetic = getAny . Foldable.foldMap (Any . isFunction)
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

-- | A 'Bottom' pattern is always 'Function'.
instance Synthetic (Bottom sort) Function where
    synthetic = const (Function True)
    {-# INLINE synthetic #-}

-- | An 'Application' pattern is 'Function' if its symbol is a function and its
-- arguments are 'Function'.
instance Synthetic (Application Internal.Symbol) Function where
    synthetic application =
        functionSymbol <> Foldable.fold children
      where
        functionSymbol = Function (Internal.isFunction symbol)
        children = applicationChildren application
        symbol = applicationSymbolOrAlias application

instance Synthetic (Application Internal.Alias) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Ceil sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

-- | A 'DomainValue' pattern is 'Function' if its argument is 'Function'.
instance Synthetic (DomainValue sort) Function where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic (Equals sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Exists sort variable) Function where
    synthetic = const (Function False)

instance Synthetic (Floor sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Forall sort variable) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Iff sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Implies sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (In sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Mu sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Next sort) Function where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic (Not sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Nu sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Or sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

instance Synthetic (Rewrites sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is 'Function' if its subterms are 'Function'.
instance Synthetic (Builtin key) Function where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic (Top sort) Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'Function'.
instance Synthetic StringLiteral Function where
    synthetic = const (Function True)
    {-# INLINE synthetic #-}

-- | A 'CharLiteral' pattern is always 'Function'.
instance Synthetic CharLiteral Function where
    synthetic = const (Function True)
    {-# INLINE synthetic #-}

-- | An 'Inhabitant' pattern is never 'Function'.
instance Synthetic Inhabitant Function where
    synthetic = const (Function False)
    {-# INLINE synthetic #-}

-- | A 'Variable' pattern is always 'Function'.
instance Synthetic (Const (UnifiedVariable variable)) Function where
    synthetic (Const (ElemVar _)) = Function True
    synthetic (Const (SetVar _)) = Function False
    {-# INLINE synthetic #-}
