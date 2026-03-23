{- |
Module      : Kore.Builtin.Float
Description : Built-in IEEE floating-point sort
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause
-}
module Kore.Builtin.Float (
    sort,
    assertSort,
    verifiers,
    builtinFunctions,
    extractFloatDomainValue,
    asInternal,
    asPattern,
    asPartialPattern,
    parseText,
    unifyFloat,
    matchFloat,
    matchUnifyFloatEq,

    -- * keys
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

import Data.Functor.Const
import Data.HashMap.Strict qualified as HashMap
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
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Builtin (
    UnifyEq (..),
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.Float.Float
import Kore.Builtin.Int qualified as Int
import Kore.Builtin.String qualified as String
import Kore.Error qualified
import Kore.Internal.InternalFloat
import Kore.Internal.InternalString
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike as TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify (
    BuiltinAndAxiomSimplifier,
 )
import Kore.Unification.Unify as Unify
import Prelude.Kore

assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook
        }

sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [(sort, Builtin.verifySortDecl)]

symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [ (precisionKey, Builtin.verifySymbol Int.assertSort [assertSort])
        , (exponentBitsKey, Builtin.verifySymbol Int.assertSort [assertSort])
        , (exponentKey, Builtin.verifySymbol Int.assertSort [assertSort])
        , (signKey, Builtin.verifySymbol Bool.assertSort [assertSort])
        , (isNaNKey, Builtin.verifySymbol Bool.assertSort [assertSort])
        , (negKey, Builtin.verifySymbol assertSort [assertSort])
        , (addKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (subKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (mulKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (divKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (remKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (absKey, Builtin.verifySymbol assertSort [assertSort])
        , (ceilKey, Builtin.verifySymbol assertSort [assertSort])
        , (floorKey, Builtin.verifySymbol assertSort [assertSort])
        , (truncKey, Builtin.verifySymbol assertSort [assertSort])
        ,
            ( roundKey
            , Builtin.verifySymbol assertSort [assertSort, Int.assertSort, Int.assertSort]
            )
        , (minKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (maxKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
        , (eqKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
        , (ltKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
        , (leKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
        , (gtKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
        , (geKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
        ,
            ( maxValueKey
            , Builtin.verifySymbol assertSort [Int.assertSort, Int.assertSort]
            )
        ,
            ( minValueKey
            , Builtin.verifySymbol assertSort [Int.assertSort, Int.assertSort]
            )
        ,
            ( int2FloatKey
            , Builtin.verifySymbol assertSort [Int.assertSort, Int.assertSort, Int.assertSort]
            )
        , (float2IntKey, Builtin.verifySymbol Int.assertSort [assertSort])
        , (float2StringKey, Builtin.verifySymbol String.assertSort [assertSort])
        , (string2FloatKey, Builtin.verifySymbol assertSort [String.assertSort])
        ]

patternVerifierHook :: Builtin.PatternVerifierHook
patternVerifierHook =
    Builtin.domainValuePatternVerifierHook sort patternVerifierWorker
  where
    patternVerifierWorker external =
        case externalChild of
            StringLiteral_ literal ->
                case parseText literal of
                    Just internalFloatValue ->
                        (return . InternalFloatF . Const)
                            InternalFloat
                                { internalFloatSort
                                , internalFloatValue
                                }
                    Nothing ->
                        Kore.Error.koreFail "Expected IEEE float literal"
            _ -> Kore.Error.koreFail "Expected literal string"
      where
        DomainValue{domainValueSort = internalFloatSort} = external
        DomainValue{domainValueChild = externalChild} = external

extractFloatDomainValue ::
    Text ->
    TermLike variable ->
    Maybe FloatValue
extractFloatDomainValue _ = \case
    InternalFloat_ InternalFloat{internalFloatValue} -> Just internalFloatValue
    _ -> Nothing

builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == precisionKey =
        Just $
            Builtin.unaryOperator
                extractFloatDomainValue
                Int.asPattern
                precisionKey
                precisionValue
    | key == exponentBitsKey =
        Just $
            Builtin.unaryOperator
                extractFloatDomainValue
                Int.asPattern
                exponentBitsKey
                exponentBitsValue
    | key == exponentKey =
        Just $
            Builtin.unaryOperator
                extractFloatDomainValue
                Int.asPattern
                exponentKey
                exponentValue
    | key == signKey =
        Just $
            Builtin.unaryOperator
                extractFloatDomainValue
                Bool.asPattern
                signKey
                signValue
    | key == isNaNKey =
        Just $
            Builtin.unaryOperator
                extractFloatDomainValue
                Bool.asPattern
                isNaNKey
                isNaNValue
    | key == negKey = Just $ unaryFloatOperator negKey negate negate
    | key == addKey = Just $ binaryFloatOperator addKey (+) (+)
    | key == subKey = Just $ binaryFloatOperator subKey (-) (-)
    | key == mulKey = Just $ binaryFloatOperator mulKey (*) (*)
    | key == divKey = Just $ binaryFloatOperator divKey (/) (/)
    | key == remKey = Just evalRem
    | key == absKey = Just $ unaryFloatOperator absKey abs abs
    | key == ceilKey = Just evalCeil
    | key == floorKey = Just evalFloor
    | key == truncKey = Just evalTrunc
    | key == roundKey = Just evalRound
    | key == minKey = Just evalMin
    | key == maxKey = Just evalMax
    | key == eqKey = Just $ comparator eqKey (==) (==)
    | key == ltKey = Just $ comparator ltKey (<) (<)
    | key == leKey = Just $ comparator leKey (<=) (<=)
    | key == gtKey = Just $ comparator gtKey (>) (>)
    | key == geKey = Just $ comparator geKey (>=) (>=)
    | key == maxValueKey = Just evalMaxValue
    | key == minValueKey = Just evalMinValue
    | key == int2FloatKey = Just evalInt2Float
    | key == float2IntKey = Just evalFloat2Int
    | key == float2StringKey = Just evalFloat2String
    | key == string2FloatKey = Just evalString2Float
    | otherwise = Nothing
  where
    unaryFloatOperator name onFloat onDouble =
        Builtin.unaryOperator
            extractFloatDomainValue
            asPattern
            name
            (unarySameFormat onFloat onDouble)

    comparator name onFloat onDouble =
        Builtin.binaryOperator
            extractFloatDomainValue
            asPartialBoolPattern
            name
            (binaryCompareSameFormat onFloat onDouble)

    binaryFloatOperator name onFloat onDouble =
        Builtin.binaryOperator
            extractFloatDomainValue
            asPartialPattern
            name
            (binarySameFormat onFloat onDouble)

    evalRem = Builtin.functionEvaluator evalRem0
    evalRem0 _ resultSort children =
        case children of
            [extractFloatDomainValue remKey -> Just first, extractFloatDomainValue remKey -> Just second] ->
                pure . asPartialPattern resultSort $ evalRemainder first second
            [_, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack remKey)

    evalCeil = Builtin.functionEvaluator evalCeil0
    evalCeil0 _ resultSort children =
        case children of
            [extractFloatDomainValue ceilKey -> Just value] ->
                pure . asPattern resultSort $ integralUnary ceilInteger value
            [_] -> empty
            _ -> Builtin.wrongArity (Text.unpack ceilKey)

    evalFloor = Builtin.functionEvaluator evalFloor0
    evalFloor0 _ resultSort children =
        case children of
            [extractFloatDomainValue floorKey -> Just value] ->
                pure . asPattern resultSort $ integralUnary floorInteger value
            [_] -> empty
            _ -> Builtin.wrongArity (Text.unpack floorKey)

    evalTrunc = Builtin.functionEvaluator evalTrunc0
    evalTrunc0 _ resultSort children =
        case children of
            [extractFloatDomainValue truncKey -> Just value] ->
                pure . asPattern resultSort $ integralUnary truncateInteger value
            [_] -> empty
            _ -> Builtin.wrongArity (Text.unpack truncKey)

    evalRound = Builtin.functionEvaluator evalRound0
    evalRound0 _ resultSort children =
        case children of
            [ extractFloatDomainValue roundKey -> Just value
                , Int.extractIntDomainValue roundKey -> Just precisionBits'
                , Int.extractIntDomainValue roundKey -> Just exponentBits'
                ] ->
                    pure . asPartialPattern resultSort $
                        do
                            format <- formatFromBits precisionBits' exponentBits'
                            pure (convertFormat format value)
            [_, _, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack roundKey)

    evalMin = Builtin.functionEvaluator evalMin0
    evalMin0 _ resultSort children =
        case children of
            [extractFloatDomainValue minKey -> Just first, extractFloatDomainValue minKey -> Just second] ->
                pure . asPartialPattern resultSort $ minFloat first second
            [_, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack minKey)

    evalMax = Builtin.functionEvaluator evalMax0
    evalMax0 _ resultSort children =
        case children of
            [extractFloatDomainValue maxKey -> Just first, extractFloatDomainValue maxKey -> Just second] ->
                pure . asPartialPattern resultSort $ maxFloat first second
            [_, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack maxKey)

    evalMaxValue = Builtin.functionEvaluator evalMaxValue0
    evalMaxValue0 _ resultSort children =
        case children of
            [ Int.extractIntDomainValue maxValueKey -> Just precisionBits'
                , Int.extractIntDomainValue maxValueKey -> Just exponentBits'
                ] ->
                    pure . asPartialPattern resultSort $
                        maxValueForFormat <$> formatFromBits precisionBits' exponentBits'
            [_, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack maxValueKey)

    evalMinValue = Builtin.functionEvaluator evalMinValue0
    evalMinValue0 _ resultSort children =
        case children of
            [ Int.extractIntDomainValue minValueKey -> Just precisionBits'
                , Int.extractIntDomainValue minValueKey -> Just exponentBits'
                ] ->
                    pure . asPartialPattern resultSort $
                        minValueForFormat <$> formatFromBits precisionBits' exponentBits'
            [_, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack minValueKey)

    evalInt2Float = Builtin.functionEvaluator evalInt2Float0
    evalInt2Float0 _ resultSort children =
        case children of
            [ Int.extractIntDomainValue int2FloatKey -> Just integerValue
                , Int.extractIntDomainValue int2FloatKey -> Just precisionBits'
                , Int.extractIntDomainValue int2FloatKey -> Just exponentBits'
                ] ->
                    pure . asPartialPattern resultSort $
                        integerToFormat <$> formatFromBits precisionBits' exponentBits' <*> pure integerValue
            [_, _, _] -> empty
            _ -> Builtin.wrongArity (Text.unpack int2FloatKey)

    evalFloat2Int = Builtin.functionEvaluator evalFloat2Int0
    evalFloat2Int0 _ resultSort children =
        case children of
            [extractFloatDomainValue float2IntKey -> Just value] ->
                pure . Int.asPartialPattern resultSort $ floatToInteger value
            [_] -> empty
            _ -> Builtin.wrongArity (Text.unpack float2IntKey)

    evalFloat2String = Builtin.functionEvaluator evalFloat2String0
    evalFloat2String0 _ resultSort children =
        case children of
            [extractFloatDomainValue float2StringKey -> Just value] ->
                pure . String.asPattern resultSort $ renderFloatValue value
            [_] -> empty
            _ -> Builtin.wrongArity (Text.unpack float2StringKey)

    evalString2Float = Builtin.functionEvaluator evalString2Float0
    evalString2Float0 _ resultSort children =
        case children of
            [extractStringDomainValue string2FloatKey -> Just input] ->
                pure . asPartialPattern resultSort $ parseText input
            [_] -> empty
            _ -> Builtin.wrongArity (Text.unpack string2FloatKey)

    integralUnary ::
        (forall b. RealFrac b => b -> Integer) ->
        FloatValue ->
        FloatValue
    integralUnary rounder = \case
        Float32 wordValue ->
            let value = castWord32ToFloat wordValue
             in if isNaN value || isInfinite value
                    then Float32 wordValue
                    else integerToFormat Binary32 (rounder value)
        Float64 wordValue ->
            let value = castWord64ToDouble wordValue
             in if isNaN value || isInfinite value
                    then Float64 wordValue
                    else integerToFormat Binary64 (rounder value)

    evalRemainder first second =
        case (first, second) of
            (Float32 word1, Float32 word2) ->
                pure . Float32 . castFloatToWord32 $
                    remainderLike (castWord32ToFloat word1) (castWord32ToFloat word2)
            (Float64 word1, Float64 word2) ->
                pure . Float64 . castDoubleToWord64 $
                    remainderLike (castWord64ToDouble word1) (castWord64ToDouble word2)
            _ -> Nothing

    remainderLike ::
        forall a.
        RealFloat a =>
        a ->
        a ->
        a
    remainderLike numerator denominator
        | isNaN numerator || isNaN denominator = 0 / 0
        | isInfinite numerator = 0 / 0
        | denominator == 0 = 0 / 0
        | isInfinite denominator = numerator
        | otherwise =
            let quotient = numerator / denominator
                nearestInteger = fromInteger (round quotient)
             in numerator - nearestInteger * denominator

    minFloat first second
        | isNaNValue first || isNaNValue second = Nothing
        | otherwise =
            case binaryCompareSameFormat compareMin compareMin first second of
                Just True -> Just first
                Just False -> Just second
                Nothing -> Nothing
      where
        compareMin x y = x < y

    maxFloat first second
        | isNaNValue first || isNaNValue second = Nothing
        | otherwise =
            case binaryCompareSameFormat compareMax compareMax first second of
                Just True -> Just first
                Just False -> Just second
                Nothing -> Nothing
      where
        compareMax x y = x > y

data UnifyFloat = UnifyFloat
    { float1, float2 :: !InternalFloat
    , term1, term2 :: !(TermLike RewritingVariableName)
    }

matchFloat ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyFloat
matchFloat term1 term2
    | InternalFloat_ float1 <- term1
    , InternalFloat_ float2 <- term2 =
        Just UnifyFloat{float1, float2, term1, term2}
    | otherwise = Nothing

unifyFloat ::
    forall unifier.
    MonadUnify unifier =>
    UnifyFloat ->
    unifier (Pattern RewritingVariableName)
unifyFloat unifyData =
    assert (on (==) internalFloatSort float1 float2) worker
  where
    worker
        | on (==) internalFloatValue float1 float2 =
            pure (Pattern.fromTermLike term1)
        | otherwise =
            debugUnifyBottomAndReturnBottom "distinct floating-point values" term1 term2
    UnifyFloat{float1, float2, term1, term2} = unifyData

matchUnifyFloatEq ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEq
matchUnifyFloatEq = Builtin.matchUnifyEq eqKey

asPartialBoolPattern ::
    InternalVariable variable =>
    Sort ->
    Maybe Bool ->
    Pattern variable
asPartialBoolPattern resultSort =
    maybe (Pattern.bottomOf resultSort) (Bool.asPattern resultSort)

extractStringDomainValue ::
    Text ->
    TermLike variable ->
    Maybe Text
extractStringDomainValue _ = \case
    TermLike.InternalString_ InternalString{internalStringValue} -> Just internalStringValue
    _ -> Nothing

ceilInteger :: RealFrac a => a -> Integer
ceilInteger = ceiling

floorInteger :: RealFrac a => a -> Integer
floorInteger = floor

truncateInteger :: RealFrac a => a -> Integer
truncateInteger = truncate
