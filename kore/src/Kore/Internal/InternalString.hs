{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Internal.InternalString (
    InternalString (..),
) where

import Data.Functor.Const
import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Pattern.Simplified
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.StringLiteral
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

-- | Internal representation of the builtin @STRING.String@ domain.
data InternalString = InternalString
    { internalStringSort :: !Sort
    , internalStringValue :: !Text
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse InternalString where
    unparse InternalString{internalStringSort, internalStringValue} =
        "\\dv"
            <> parameters [internalStringSort]
            <> Pretty.parens (unparse $ StringLiteral internalStringValue)

    unparse2 InternalString{internalStringSort, internalStringValue} =
        "\\dv2"
            <> parameters2 [internalStringSort]
            <> arguments2 [StringLiteral internalStringValue]

instance Synthetic Sort (Const InternalString) where
    synthetic (Const InternalString{internalStringSort}) = internalStringSort
    {-# INLINE synthetic #-}

instance Synthetic (FreeVariables variable) (Const InternalString) where
    synthetic _ = emptyFreeVariables
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLike (Const InternalString) where
    synthetic _ = ConstructorLike . Just $ ConstructorLikeHead
    {-# INLINE synthetic #-}

instance Synthetic Defined (Const InternalString) where
    synthetic = alwaysDefined
    {-# INLINE synthetic #-}

instance Synthetic Function (Const InternalString) where
    synthetic = alwaysFunction
    {-# INLINE synthetic #-}

instance Synthetic Functional (Const InternalString) where
    synthetic = alwaysFunctional
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const InternalString) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}
