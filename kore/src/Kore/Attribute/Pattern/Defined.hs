{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Defined
    ( Defined (..)
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

{- | A pattern is 'Defined' if it matches at least one element.
 -}
newtype Defined = Defined { isDefined :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)
    deriving (Semigroup, Monoid) via All

instance SOP.Generic Defined

instance SOP.HasDatatypeInfo Defined

instance Debug Defined

instance Diff Defined

instance NFData Defined

instance Hashable Defined

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
        functionSymbol <> Foldable.fold children
      where
        functionSymbol = Defined (Internal.isTotal symbol)
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
    synthetic = Defined . getAny . Foldable.foldMap (Any . isDefined)
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
instance Synthetic Defined (Top sort) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | A 'StringLiteral' pattern is always 'Defined'.
instance Synthetic Defined (Const StringLiteral) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | An 'Inhabitant' pattern is always 'Defined'.
instance Synthetic Defined Inhabitant where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

-- | An element variable pattern is always 'Defined'.
--   A set variable is not.
instance Synthetic Defined (Const (UnifiedVariable variable)) where
    synthetic (Const (ElemVar _))= Defined True
    synthetic (Const (SetVar _))= Defined False
    {-# INLINE synthetic #-}
