{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause
-}
module Kore.Internal.InternalFloat (
    FloatValue (..),
    InternalFloat (..),
    precisionBits,
    exponentBits,
    renderExactFloatValue,
    renderFloatValue,
) where

import Data.Functor.Const
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Data.Word (
    Word32,
    Word64,
 )
import GHC.Float (
    castWord32ToFloat,
    castWord64ToDouble,
 )
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Simplified
import Kore.Attribute.Pattern.Total
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Numeric (
    showGFloat,
 )
import Prelude.Kore
import Pretty qualified

data FloatValue
    = Float32 !Word32
    | Float64 !Word64
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

precisionBits :: FloatValue -> Integer
precisionBits = \case
    Float32 _ -> 24
    Float64 _ -> 53

exponentBits :: FloatValue -> Integer
exponentBits = \case
    Float32 _ -> 8
    Float64 _ -> 11

renderFloatValue :: FloatValue -> Text
renderFloatValue = \case
    value | isNaNValue value -> renderExactFloatValue value
    Float32 value ->
        prettyRealFloat (castWord32ToFloat value) <> "f"
    Float64 value ->
        prettyRealFloat (castWord64ToDouble value)
  where
    prettyRealFloat :: RealFloat a => a -> Text
    prettyRealFloat value = Text.pack (showGFloat Nothing value "")

    isNaNValue = \case
        Float32 value -> isNaN (castWord32ToFloat value)
        Float64 value -> isNaN (castWord64ToDouble value)

renderExactFloatValue :: FloatValue -> Text
renderExactFloatValue = \case
    Float32 value -> "bits32(" <> showDecimal value <> ")"
    Float64 value -> "bits64(" <> showDecimal value <> ")"
  where
    showDecimal :: Show a => a -> Text
    showDecimal = Text.pack . show

-- | Internal representation of the builtin @FLOAT.Float@ domain.
data InternalFloat = InternalFloat
    { internalFloatSort :: !Sort
    , internalFloatValue :: !FloatValue
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse InternalFloat where
    unparse InternalFloat{internalFloatSort, internalFloatValue} =
        "\\dv"
            <> parameters [internalFloatSort]
            <> Pretty.parens (Pretty.dquotes $ Pretty.pretty $ renderFloatValue internalFloatValue)

    unparse2 InternalFloat{internalFloatSort, internalFloatValue} =
        "\\dv2"
            <> parameters2 [internalFloatSort]
            <> arguments' [Pretty.dquotes $ Pretty.pretty $ renderFloatValue internalFloatValue]

instance Synthetic Sort (Const InternalFloat) where
    synthetic (Const InternalFloat{internalFloatSort}) = internalFloatSort

instance Synthetic (FreeVariables variable) (Const InternalFloat) where
    synthetic _ = emptyFreeVariables

instance Synthetic ConstructorLike (Const InternalFloat) where
    synthetic = const (ConstructorLike . Just $ ConstructorLikeHead)
    {-# INLINE synthetic #-}

instance Synthetic Defined (Const InternalFloat) where
    synthetic = alwaysDefined
    {-# INLINE synthetic #-}

instance Synthetic Function (Const InternalFloat) where
    synthetic = alwaysFunction
    {-# INLINE synthetic #-}

instance Synthetic Total (Const InternalFloat) where
    synthetic = alwaysTotal
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const InternalFloat) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}
