{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Defined
    ( Defined (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
import Data.Functor.Const
import qualified Data.Map.Strict as Map
import Data.Monoid
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Builtin
import qualified Kore.Internal.Alias as Internal
import Kore.Internal.Inj
    ( Inj
    )
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.InternalBytes
    ( InternalBytes
    )
import Kore.Internal.InternalInt
    ( InternalInt
    )
import qualified Kore.Internal.Symbol as Internal
import Kore.Syntax

{- | A pattern is 'Defined' if it matches at least one element.
 -}
newtype Defined = Defined { isDefined :: Bool }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving (Semigroup, Monoid) via All

instance Synthetic Defined (And sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Bottom sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | An 'Application' pattern is 'Defined' if the symbol is total and its
-- arguments are 'Defined'.
instance Synthetic Defined (Application Internal.Symbol) where
    synthetic application =
        totalSymbol <> fold children
      where
        totalSymbol = Defined (Internal.isTotal symbol)
        children = applicationChildren application
        symbol = applicationSymbolOrAlias application

-- TODO: calculate by looking at RHS of alias
instance Synthetic Defined (Application (Internal.Alias patternType)) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Ceil sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | A 'DomainValue' patterns is 'Defined' if its argument is 'Defined'.
instance Synthetic Defined (DomainValue sort) where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic Defined (Equals sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Exists sort variable) where
    synthetic = const (Defined False)

instance Synthetic Defined (Floor sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Forall sort variable) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Iff sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Implies sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (In sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Mu sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | A 'Next' pattern is 'Defined' if its argument is 'Defined'.
instance Synthetic Defined (Next sort) where
    synthetic = nextChild
    {-# INLINE synthetic #-}

instance Synthetic Defined (Not sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Nu sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | An 'Or' pattern is 'Defined' if any of its subterms is 'Defined'.
instance Synthetic Defined (Or sort) where
    synthetic = Defined . getAny . foldMap (Any . isDefined)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Rewrites sort) where
    synthetic = const (Defined False)
    {-# INLINE synthetic #-}

-- | A 'Builtin' pattern is defined if its subterms are 'Defined'.
instance Synthetic Defined (Builtin key) where
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
    synthetic builtin = fold builtin
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
    sameAsChildren = fold ac


-- | A 'Top' pattern is always 'Defined'.
instance Synthetic Defined (Top sort) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'Defined'.
instance Synthetic Defined (Const StringLiteral) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | An 'InternalBytes' pattern is always 'Defined'.
instance Synthetic Defined (Const InternalBytes) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | A 'InternalInt' pattern is always 'Defined'.
instance Synthetic Defined (Const InternalInt) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | An 'Inhabitant' pattern is always 'Defined'.
instance Synthetic Defined Inhabitant where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | An element variable pattern is always 'Defined'.
--   A set variable is not.
instance Synthetic Defined (Const (SomeVariable variable)) where
    synthetic (Const unifiedVariable)= Defined (isElementVariable unifiedVariable)
    {-# INLINE synthetic #-}

instance Synthetic Defined Inj where
    synthetic = synthetic . Inj.toApplication
