{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause
-}
module Kore.Builtin.Float.Float (
    FloatFormat (..),
    sort,
    asBuiltin,
    asInternal,
    asPattern,
    asPartialPattern,
    parseText,
    convertFormat,
    formatFromBits,
    precisionValue,
    exponentBitsValue,
    exponentValue,
    signValue,
    isNaNValue,
    unarySameFormat,
    binarySameFormat,
    binaryCompareSameFormat,
    minValueForFormat,
    maxValueForFormat,
    floatToInteger,
    integerToFormat,
    roundToIntegral,

    -- * Keys
    precisionKey,
    exponentBitsKey,
    exponentKey,
    signKey,
    isNaNKey,
    negKey,
    addKey,
    subKey,
    mulKey,
    divKey,
    remKey,
    absKey,
    ceilKey,
    floorKey,
    truncKey,
    roundKey,
    minKey,
    maxKey,
    eqKey,
    ltKey,
    leKey,
    gtKey,
    geKey,
    maxValueKey,
    minValueKey,
    int2FloatKey,
    float2IntKey,
    float2StringKey,
    string2FloatKey,
) where

import Control.Monad (
    guard,
 )
import Data.Bits (
    shiftR,
    (.&.),
 )
import Data.Char qualified as Char
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import GHC.Float (
    castDoubleToWord64,
    castFloatToWord32,
    castWord32ToFloat,
    castWord64ToDouble,
 )
import Kore.Internal.InternalFloat
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike as TermLike
import Prelude.Kore
import Text.Read (
    readMaybe,
 )

data FloatFormat = Binary32 | Binary64
    deriving stock (Eq, Ord, Show)

sort :: Text
sort = "FLOAT.Float"

asBuiltin :: Sort -> FloatValue -> InternalFloat
asBuiltin = InternalFloat

asInternal ::
    Sort ->
    FloatValue ->
    TermLike variable
asInternal internalFloatSort internalFloatValue =
    TermLike.fromConcrete . mkInternalFloat $
        asBuiltin internalFloatSort internalFloatValue

asPattern ::
    InternalVariable variable =>
    Sort ->
    FloatValue ->
    Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal resultSort

asPartialPattern ::
    InternalVariable variable =>
    Sort ->
    Maybe FloatValue ->
    Pattern variable
asPartialPattern resultSort =
    maybe (Pattern.bottomOf resultSort) (asPattern resultSort)

formatOf :: FloatValue -> FloatFormat
formatOf = \case
    Float32 _ -> Binary32
    Float64 _ -> Binary64

formatFromBits :: Integer -> Integer -> Maybe FloatFormat
formatFromBits precisionBits' exponentBits'
    | (precisionBits', exponentBits') == (24, 8) = Just Binary32
    | (precisionBits', exponentBits') == (53, 11) = Just Binary64
    | otherwise = Nothing

precisionValue :: FloatValue -> Integer
precisionValue = precisionBits

exponentBitsValue :: FloatValue -> Integer
exponentBitsValue = exponentBits

exponentValue :: FloatValue -> Integer
exponentValue = \case
    Float32 wordValue -> toInteger ((wordValue `shiftR` 23) .&. 0xff)
    Float64 wordValue -> toInteger ((wordValue `shiftR` 52) .&. 0x7ff)

signValue :: FloatValue -> Bool
signValue = \case
    Float32 wordValue -> ((wordValue `shiftR` 31) .&. 0x1) == 1
    Float64 wordValue -> ((wordValue `shiftR` 63) .&. 0x1) == 1

isNaNValue :: FloatValue -> Bool
isNaNValue = \case
    Float32 wordValue -> isNaN (castWord32ToFloat wordValue)
    Float64 wordValue -> isNaN (castWord64ToDouble wordValue)

maxValueForFormat :: FloatFormat -> FloatValue
maxValueForFormat = \case
    Binary32 -> Float32 0x7f7fffff
    Binary64 -> Float64 0x7fefffffffffffff

minValueForFormat :: FloatFormat -> FloatValue
minValueForFormat = \case
    Binary32 -> Float32 0x00000001
    Binary64 -> Float64 0x0000000000000001

integerToFormat :: FloatFormat -> Integer -> FloatValue
integerToFormat = \case
    Binary32 -> \integerValue -> Float32 (castFloatToWord32 (fromInteger integerValue))
    Binary64 -> \integerValue -> Float64 (castDoubleToWord64 (fromInteger integerValue))

floatToInteger :: FloatValue -> Maybe Integer
floatToInteger = \case
    Float32 wordValue ->
        let value = castWord32ToFloat wordValue
         in if isNaN value || isInfinite value
                then Nothing
                else Just (round value)
    Float64 wordValue ->
        let value = castWord64ToDouble wordValue
         in if isNaN value || isInfinite value
                then Nothing
                else Just (round value)

roundToIntegral :: FloatValue -> FloatValue
roundToIntegral = \case
    Float32 wordValue ->
        let value = castWord32ToFloat wordValue
         in if isNaN value || isInfinite value
                then Float32 wordValue
                else Float32 (castFloatToWord32 (fromInteger (round value)))
    Float64 wordValue ->
        let value = castWord64ToDouble wordValue
         in if isNaN value || isInfinite value
                then Float64 wordValue
                else Float64 (castDoubleToWord64 (fromInteger (round value)))

convertFormat :: FloatFormat -> FloatValue -> FloatValue
convertFormat target value
    | target == formatOf value = value
convertFormat Binary32 (Float64 wordValue) =
    Float32 (castFloatToWord32 (realToFrac (castWord64ToDouble wordValue)))
convertFormat Binary64 (Float32 wordValue) =
    Float64 (castDoubleToWord64 (realToFrac (castWord32ToFloat wordValue)))
convertFormat Binary32 (Float32 wordValue) = Float32 wordValue
convertFormat Binary64 (Float64 wordValue) = Float64 wordValue

unarySameFormat ::
    (Float -> Float) ->
    (Double -> Double) ->
    FloatValue ->
    FloatValue
unarySameFormat onFloat onDouble = \case
    Float32 wordValue ->
        Float32 (castFloatToWord32 (onFloat (castWord32ToFloat wordValue)))
    Float64 wordValue ->
        Float64 (castDoubleToWord64 (onDouble (castWord64ToDouble wordValue)))

binarySameFormat ::
    (Float -> Float -> Float) ->
    (Double -> Double -> Double) ->
    FloatValue ->
    FloatValue ->
    Maybe FloatValue
binarySameFormat onFloat onDouble first second =
    case (first, second) of
        (Float32 word1, Float32 word2) ->
            Just . Float32 $
                castFloatToWord32
                    (onFloat (castWord32ToFloat word1) (castWord32ToFloat word2))
        (Float64 word1, Float64 word2) ->
            Just . Float64 $
                castDoubleToWord64
                    (onDouble (castWord64ToDouble word1) (castWord64ToDouble word2))
        _ -> Nothing

binaryCompareSameFormat ::
    (Float -> Float -> Bool) ->
    (Double -> Double -> Bool) ->
    FloatValue ->
    FloatValue ->
    Maybe Bool
binaryCompareSameFormat onFloat onDouble first second =
    case (first, second) of
        (Float32 word1, Float32 word2) ->
            Just (onFloat (castWord32ToFloat word1) (castWord32ToFloat word2))
        (Float64 word1, Float64 word2) ->
            Just (onDouble (castWord64ToDouble word1) (castWord64ToDouble word2))
        _ -> Nothing

parseText :: Text -> Maybe FloatValue
parseText input = do
    (body, format) <- parseFormat input
    case format of
        Binary32 ->
            Float32 . castFloatToWord32 <$> readMaybe (Text.unpack body)
        Binary64 ->
            Float64 . castDoubleToWord64 <$> readMaybe (Text.unpack body)

parseFormat :: Text -> Maybe (Text, FloatFormat)
parseFormat input =
    case Text.unsnoc input of
        Just (body, suffix)
            | suffix == 'f' || suffix == 'F' -> Just (body, Binary32)
            | suffix == 'd' || suffix == 'D' -> Just (body, Binary64)
        _ ->
            case parseExplicitFormat input of
                Just explicit -> Just explicit
                Nothing -> Just (input, Binary64)

parseExplicitFormat :: Text -> Maybe (Text, FloatFormat)
parseExplicitFormat input = do
    let (rest1, expBitsText) = splitTrailingDigits input
    (rest2, xChar) <- Text.unsnoc rest1
    guard (xChar == 'x' || xChar == 'X')
    guard (not (Text.null expBitsText))
    let (rest3, precisionText) = splitTrailingDigits rest2
    (body, pChar) <- Text.unsnoc rest3
    guard (pChar == 'p' || pChar == 'P')
    guard (not (Text.null precisionText))
    precisionBits' <- readMaybe (Text.unpack precisionText)
    exponentBits' <- readMaybe (Text.unpack expBitsText)
    format <- formatFromBits precisionBits' exponentBits'
    pure (body, format)
  where
    splitTrailingDigits text =
        let reversed = Text.reverse text
            trailingDigitsReversed = Text.takeWhile Char.isDigit reversed
            trailingDigits = Text.reverse trailingDigitsReversed
            prefix = Text.dropEnd (Text.length trailingDigits) text
         in (prefix, trailingDigits)

precisionKey, exponentBitsKey, exponentKey, signKey, isNaNKey :: IsString s => s
precisionKey = "FLOAT.precision"
exponentBitsKey = "FLOAT.exponentBits"
exponentKey = "FLOAT.exponent"
signKey = "FLOAT.sign"
isNaNKey = "FLOAT.isNaN"

negKey, addKey, subKey, mulKey, divKey, remKey :: IsString s => s
negKey = "FLOAT.neg"
addKey = "FLOAT.add"
subKey = "FLOAT.sub"
mulKey = "FLOAT.mul"
divKey = "FLOAT.div"
remKey = "FLOAT.rem"

absKey, ceilKey, floorKey, truncKey, roundKey, minKey, maxKey :: IsString s => s
absKey = "FLOAT.abs"
ceilKey = "FLOAT.ceil"
floorKey = "FLOAT.floor"
truncKey = "FLOAT.trunc"
roundKey = "FLOAT.round"
minKey = "FLOAT.min"
maxKey = "FLOAT.max"

eqKey, ltKey, leKey, gtKey, geKey :: IsString s => s
eqKey = "FLOAT.eq"
ltKey = "FLOAT.lt"
leKey = "FLOAT.le"
gtKey = "FLOAT.gt"
geKey = "FLOAT.ge"

maxValueKey, minValueKey, int2FloatKey, float2IntKey :: IsString s => s
maxValueKey = "FLOAT.maxValue"
minValueKey = "FLOAT.minValue"
int2FloatKey = "FLOAT.int2float"
float2IntKey = "FLOAT.float2int"

float2StringKey, string2FloatKey :: IsString s => s
float2StringKey = "STRING.float2string"
string2FloatKey = "STRING.string2float"
