{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Functional
    ( Functional (..)
    ) where

import Control.DeepSeq
import qualified Data.Foldable as Foldable
import Data.Functor.Const
import Data.Hashable
import qualified Data.Map as Map
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

{- | A pattern is 'Functional' if it matches exactly one element.
 -}
newtype Functional = Functional { isFunctional :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Functional

instance SOP.HasDatatypeInfo Functional

instance Debug Functional

instance Diff Functional

instance NFData Functional

instance Hashable Functional

instance Synthetic Functional (And sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

instance Synthetic Functional (Bottom sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | An 'Application' pattern is 'Functional' if its symbol is functional and
-- its arguments are 'Functional'.
instance Synthetic Functional (Application Internal.Symbol) where
    synthetic application =
        functionalSymbol <> Foldable.fold children
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

-- | A 'Builtin' pattern is 'Functional' if its subterms are 'Functional'.
instance Synthetic Functional (Builtin key) where
    synthetic
        (BuiltinSet InternalAc
            {builtinAcChild = NormalizedSet builtinSetChild}
        )
      = normalizedAcFunctional builtinSetChild
    synthetic
        (BuiltinMap InternalAc
            {builtinAcChild = NormalizedMap builtinMapChild}
        )
      = normalizedAcFunctional builtinMapChild
    synthetic builtin = Foldable.fold builtin
    {-# INLINE synthetic #-}

normalizedAcFunctional
    :: (Foldable (Element collection), Foldable (Value collection))
    => NormalizedAc collection key Functional -> Functional
normalizedAcFunctional ac@(NormalizedAc _ _ _) =
    case ac of
        NormalizedAc
            { elementsWithVariables = []
            , opaque = []
            } -> sameAsChildren
        NormalizedAc
            { elementsWithVariables = [_]
            , concreteElements
            , opaque = []
            }
          | Map.null concreteElements -> sameAsChildren
        NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = [_]
            }
          | Map.null concreteElements -> sameAsChildren
        _ -> Functional False
  where
    sameAsChildren = Foldable.fold ac

instance Synthetic Functional (Top sort) where
    synthetic = const (Functional False)
    {-# INLINE synthetic #-}

-- | A 'Variable' pattern is always 'Functional'.
instance Synthetic Functional (Const (UnifiedVariable variable)) where
    synthetic (Const (ElemVar _)) = Functional True
    synthetic (Const (SetVar _)) = Functional False
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
