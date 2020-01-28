{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Builtin.Signedness.Signedness
    ( Signedness (..)
    , toApplication
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import Data.Functor.Const
import Data.Hashable
    ( Hashable
    )
import Data.Void
    ( Void
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Pattern.Simplified
import Kore.Attribute.Synthetic
import Kore.Internal.Symbol
import Kore.Sort
import Kore.Syntax.Application
    ( Application (..)
    )
import Kore.Unparser

data Signedness
    = Signed !Symbol
    | Unsigned !Symbol
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance Hashable Signedness

instance NFData Signedness

instance SOP.Generic Signedness

instance SOP.HasDatatypeInfo Signedness

instance Debug Signedness

instance Diff Signedness

instance Unparse Signedness where
    unparse = unparse . toApplication @Void
    unparse2 = unparse2 . toApplication @Void

instance
    Ord variable
    => Synthetic (FreeVariables variable) (Const Signedness)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance Synthetic Sort (Const Signedness) where
    synthetic = synthetic . toApplication . getConst
    {-# INLINE synthetic #-}

instance Synthetic Functional (Const Signedness) where
    synthetic = const (Functional True)
    {-# INLINE synthetic #-}

instance Synthetic Function (Const Signedness) where
    synthetic = const (Function True)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Const Signedness) where
    synthetic = const (Defined True)
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const Signedness) where
    synthetic = const fullySimplified
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLike (Const Signedness) where
    synthetic =
        -- Signedness symbols are constructors
        const (ConstructorLike (Just ConstructorLikeHead))
    {-# INLINE synthetic #-}

toSymbol :: Signedness -> Symbol
toSymbol (Signed symbol) = symbol
toSymbol (Unsigned symbol) = symbol

toApplication :: forall child. Signedness -> Application Symbol child
toApplication signedness = Application (toSymbol signedness) []
