{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Defined
    ( Defined (..)
    ) where

import           Control.DeepSeq
import qualified Data.Foldable as Foldable
import           Data.Functor.Const
import           Data.Hashable
import qualified Data.Map as Map
import           Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import           Kore.Attribute.Synthetic
import           Kore.Debug
import           Kore.Domain.Builtin
import qualified Kore.Internal.Alias as Internal
import qualified Kore.Internal.Symbol as Internal
import           Kore.Syntax

{- | A pattern is 'Defined' if it matches at least one element.
 -}
newtype Defined = Defined { isDefined :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Defined

instance SOP.HasDatatypeInfo Defined

instance Debug Defined

instance NFData Defined

instance Hashable Defined

instance Synthetic (And sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Bottom sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | An 'Application' pattern is 'Defined' if the symbol is total and its
-- arguments are 'Defined'.
instance Synthetic (Application Internal.Symbol) Defined where
    synthetic application =
        functionSymbol <> Foldable.fold children
      where
        functionSymbol = Defined (Internal.isTotal symbol)
        children = applicationChildren application
        symbol = applicationSymbolOrAlias application

instance Synthetic (Application Internal.Alias) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Ceil sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | A 'DomainValue' patterns is 'Defined' if its argument is 'Defined'.
instance Synthetic (DomainValue sort) Defined where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic (Equals sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Exists sort variable) Defined where
    synthetic = const (Defined False)

instance Synthetic (Floor sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Forall sort variable) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Iff sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Implies sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (In sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Mu sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | A 'Next' pattern is 'Defined' if its argument is 'Defined'.
instance Synthetic (Next sort) Defined where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic (Not sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic (Nu sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | An 'Or' pattern is 'Defined' if any of its subterms is 'Defined'.
instance Synthetic (Or sort) Defined where
    synthetic = Defined . getAny . Foldable.foldMap (Any . isDefined)
    {-# INLINE synthetic #-}

instance Synthetic (Rewrites sort) Defined where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is defined if its subterms are 'Defined'.
instance Synthetic (Builtin key) Defined where
    synthetic
        (BuiltinSet InternalAc
            {builtinAcChild = NormalizedSet builtinSetChild}
        )
      = normalizedAcDefined builtinSetChild
    synthetic
        (BuiltinMap InternalAc
            {builtinAcChild = NormalizedMap builtinMapChild}
        )
      = normalizedAcDefined builtinMapChild
    synthetic builtin = Foldable.fold builtin
    {-# INLINE synthetic #-}

normalizedAcDefined
    :: (Foldable (Element collection), Foldable (Value collection))
    => NormalizedAc collection key Defined -> Defined
normalizedAcDefined ac@(NormalizedAc _ _ _) =
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
        _ -> Defined False
  where
    sameAsChildren = Foldable.fold ac


-- | A 'Top' pattern is always 'Defined'.
instance Synthetic (Top sort) Defined where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'Defined'.
instance Synthetic StringLiteral Defined where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | A 'CharLiteral' pattern is always 'Defined'.
instance Synthetic CharLiteral Defined where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | An 'Inhabitant' pattern is always 'Defined'.
instance Synthetic Inhabitant Defined where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | A 'Variable' pattern is always 'Defined'.
instance Synthetic (Const Variable) Defined where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}
