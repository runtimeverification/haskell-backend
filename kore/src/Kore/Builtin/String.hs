{- |
Module      : Kore.Builtin.String
Description : Built-in string sort
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.String as String
@
-}
module Kore.Builtin.String (
    sort,
    assertSort,
    verifiers,
    builtinFunctions,
    expectBuiltinString,
    asInternal,
    asPattern,
    asPartialPattern,
    parse,
    unifyString,
    matchString,
    matchUnifyStringEq,

    -- * keys
    ltKey,
    plusKey,
    string2IntKey,
    int2StringKey,
    substrKey,
    lengthKey,
    findKey,
    string2BaseKey,
    chrKey,
    ordKey,
    token2StringKey,
    string2TokenKey,
) where

import Control.Error (
    MaybeT,
 )
import Data.Char as Char (
    chr,
    isAsciiLower,
    isAsciiUpper,
    isDigit,
    ord,
 )
import Data.Functor.Const
import Data.HashMap.Strict qualified as HashMap
import Data.List (
    findIndex,
 )
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Data.Text.Read qualified as Text
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Builtin (
    UnifyEq (..),
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.Int qualified as Int
import Kore.Builtin.String.String
import Kore.Error qualified
import Kore.Internal.ApplicationSorts (
    applicationSortsResult,
 )
import Kore.Internal.InternalString
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike as TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Log.WarnNotImplemented
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify (
    BuiltinAndAxiomSimplifier,
 )
import Kore.Unification.Unify as Unify
import Numeric (
    readInt,
    showIntAtBase,
    showSigned,
 )
import Prelude.Kore
import Text.Megaparsec qualified as Parsec

{- | Verify that the sort is hooked to the builtin @String@ sort.

  See also: 'sort', 'Builtin.verifySort'
-}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook
        }

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'
-}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [(sort, Builtin.verifySortDecl)]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'
-}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [
            ( eqKey
            , Builtin.verifySymbol Bool.assertSort [assertSort, assertSort]
            )
        ,
            ( ltKey
            , Builtin.verifySymbol Bool.assertSort [assertSort, assertSort]
            )
        ,
            ( plusKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( substrKey
            , Builtin.verifySymbol
                assertSort
                [assertSort, Int.assertSort, Int.assertSort]
            )
        ,
            ( lengthKey
            , Builtin.verifySymbol Int.assertSort [assertSort]
            )
        ,
            ( findKey
            , Builtin.verifySymbol
                Int.assertSort
                [assertSort, assertSort, Int.assertSort]
            )
        ,
            ( string2BaseKey
            , Builtin.verifySymbol
                Int.assertSort
                [assertSort, Int.assertSort]
            )
        ,
            ( base2StringKey
            , Builtin.verifySymbol
                assertSort
                [Int.assertSort, Int.assertSort]
            )
        ,
            ( string2IntKey
            , Builtin.verifySymbol Int.assertSort [assertSort]
            )
        ,
            ( int2StringKey
            , Builtin.verifySymbol assertSort [Int.assertSort]
            )
        ,
            ( chrKey
            , Builtin.verifySymbol assertSort [Int.assertSort]
            )
        ,
            ( ordKey
            , Builtin.verifySymbol Int.assertSort [assertSort]
            )
        ,
            ( token2StringKey
            , Builtin.verifySymbol
                assertSort
                [Builtin.verifySortHasDomainValues]
            )
        ,
            ( string2TokenKey
            , Builtin.verifySymbol
                Builtin.verifySortHasDomainValues
                [assertSort]
            )
        ]

-- | Verify that domain value patterns are well-formed.
patternVerifierHook :: Builtin.PatternVerifierHook
patternVerifierHook =
    Builtin.domainValuePatternVerifierHook sort patternVerifierWorker
  where
    patternVerifierWorker domainValue =
        case externalChild of
            StringLiteral_ internalStringValue ->
                (return . InternalStringF . Const)
                    InternalString
                        { internalStringSort
                        , internalStringValue
                        }
            _ -> Kore.Error.koreFail "Expected literal string"
      where
        DomainValue{domainValueSort = internalStringSort} = domainValue
        DomainValue{domainValueChild = externalChild} = domainValue

-- | get the value from a (possibly encoded) domain value
extractStringDomainValue ::
    -- | error message context
    Text ->
    TermLike variable ->
    Maybe Text
extractStringDomainValue _ =
    \case
        InternalString_ internal ->
            Just internalStringValue
          where
            InternalString{internalStringValue} = internal
        _ -> Nothing

-- | Parse a string literal.
parse :: Builtin.Parser Text
parse = Text.pack <$> Parsec.many Parsec.anySingle

{- | Abort function evaluation if the argument is not a String domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.
-}
expectBuiltinString ::
    Monad m =>
    -- | Context for error message
    String ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m Text
expectBuiltinString _ =
    \case
        InternalString_ internal ->
            return internalStringValue
          where
            InternalString{internalStringValue} = internal
        _ -> empty

evalSubstr :: BuiltinAndAxiomSimplifier
evalSubstr = Builtin.functionEvaluator evalSubstr0
  where
    substr :: Int -> Int -> Text -> Text
    substr startIndex endIndex =
        Text.take (endIndex - startIndex) . Text.drop startIndex

    evalSubstr0 _ resultSort [_str, _start, _end] = do
        _str <- expectBuiltinString substrKey _str
        _start <- fromInteger <$> Int.expectBuiltinInt substrKey _start
        _end <- fromInteger <$> Int.expectBuiltinInt substrKey _end
        substr _start _end _str
            & asPattern resultSort
            & return
    evalSubstr0 _ _ _ = Builtin.wrongArity substrKey

evalLength :: BuiltinAndAxiomSimplifier
evalLength = Builtin.functionEvaluator evalLength0
  where
    evalLength0 _ resultSort [_str] = do
        _str <- expectBuiltinString lengthKey _str
        Text.length _str
            & toInteger
            & Int.asPattern resultSort
            & return
    evalLength0 _ _ _ = Builtin.wrongArity lengthKey

evalFind :: BuiltinAndAxiomSimplifier
evalFind = Builtin.functionEvaluator evalFind0
  where
    maybeNotFound :: Maybe Int -> Integer
    maybeNotFound = maybe (-1) toInteger

    evalFind0 _ resultSort [_str, _substr, _idx] = do
        _str <- expectBuiltinString findKey _str
        _substr <- expectBuiltinString findKey _substr
        _idx <- fromInteger <$> Int.expectBuiltinInt substrKey _idx
        let result =
                findIndex
                    (Text.isPrefixOf _substr)
                    (Text.tails . Text.drop _idx $ _str)
        maybeNotFound result
            & Int.asPattern resultSort
            & return
    evalFind0 _ _ _ = Builtin.wrongArity findKey

evalString2Base :: BuiltinAndAxiomSimplifier
evalString2Base = Builtin.applicationEvaluator evalString2Base0
  where
    evalString2Base0 _ app
        | [_strTerm, _baseTerm] <- applicationChildren app = do
            let Application{applicationSymbolOrAlias = symbol} = app
                resultSort = symbolSorts symbol & applicationSortsResult
            _str <- expectBuiltinString string2BaseKey _strTerm
            _base <- Int.expectBuiltinInt string2BaseKey _baseTerm
            unless (2 <= _base && _base <= 36) $ warnNotImplemented app >> empty
            return $ case readWithBase _base (Text.unpack _str) of
                [(result, "")] -> Int.asPattern resultSort result
                _ -> Pattern.bottomOf resultSort
    evalString2Base0 _ _ = Builtin.wrongArity string2BaseKey

readWithBase :: Integer -> ReadS Integer
readWithBase base = sign $ readInt base isValidDigit valDigit
  where
    sign p ('-' : cs) = do
        (a, str') <- p cs
        return (negate a, str')
    sign p ('+' : cs) = p cs
    sign p cs = p cs
    isValidDigit = maybe False (< base) . valDig
    valDigit = fromMaybe 0 . valDig
    valDig c
        | isDigit c = Just $ fromIntegral $ ord c - ord '0'
        | isAsciiLower c = Just $ fromIntegral $ ord c - ord 'a' + 10
        | isAsciiUpper c = Just $ fromIntegral $ ord c - ord 'A' + 10
        | otherwise = Nothing

evalBase2String :: BuiltinAndAxiomSimplifier
evalBase2String = Builtin.applicationEvaluator evalBase2String0
  where
    evalBase2String0 _ app
        | [_intTerm, _baseTerm] <- applicationChildren app = do
            let Application{applicationSymbolOrAlias = symbol} = app
                resultSort = symbolSorts symbol & applicationSortsResult
            _int <- Int.expectBuiltinInt base2StringKey _intTerm
            _base <- Int.expectBuiltinInt base2StringKey _baseTerm
            unless (2 <= _base && _base <= 36) $ warnNotImplemented app >> empty
            Text.pack (showWithBase _int _base)
                & asPattern resultSort
                & return
    evalBase2String0 _ _ = Builtin.wrongArity base2StringKey

showWithBase :: Integer -> Integer -> String
showWithBase int base = showSigned (showIntAtBase base toChar) 0 int ""
  where
    -- chr 48 == '0', chr 97 == 'a'
    toChar digit
        | 0 <= digit && digit <= 9 = chr $ digit + 48
        | otherwise = chr $ digit + 87

evalString2Int :: BuiltinAndAxiomSimplifier
evalString2Int = Builtin.functionEvaluator evalString2Int0
  where
    evalString2Int0 _ resultSort [_str] = do
        _str <- expectBuiltinString string2IntKey _str
        case Text.signed Text.decimal _str of
            Right (result, Text.unpack -> "") ->
                return (Int.asPattern resultSort result)
            _ -> return (Pattern.bottomOf resultSort)
    evalString2Int0 _ _ _ = Builtin.wrongArity string2IntKey

evalInt2String :: BuiltinAndAxiomSimplifier
evalInt2String = Builtin.functionEvaluator evalInt2String0
  where
    evalInt2String0 _ resultSort [_int] = do
        _int <- Int.expectBuiltinInt int2StringKey _int
        Text.pack (show _int)
            & asPattern resultSort
            & return
    evalInt2String0 _ _ _ = Builtin.wrongArity int2StringKey

evalChr :: BuiltinAndAxiomSimplifier
evalChr = Builtin.functionEvaluator evalChr0
  where
    evalChr0 _ resultSort [_n] = do
        _n <- Int.expectBuiltinInt chrKey _n
        Text.singleton (chr $ fromIntegral _n)
            & asPattern resultSort
            & return
    evalChr0 _ _ _ = Builtin.wrongArity chrKey

evalOrd :: BuiltinAndAxiomSimplifier
evalOrd = Builtin.functionEvaluator evalOrd0
  where
    evalOrd0 _ resultSort [_str] = do
        _str <- expectBuiltinString ordKey _str
        let result
                | Text.length _str == 1 = charToOrdInt (Text.head _str)
                | otherwise = Pattern.bottomOf resultSort
        return result
      where
        charToOrdInt =
            Int.asPattern resultSort
                . toInteger
                . ord
    evalOrd0 _ _ _ = Builtin.wrongArity ordKey

evalToken2String :: BuiltinAndAxiomSimplifier
evalToken2String = Builtin.functionEvaluator evalToken2String0
  where
    evalToken2String0 _ resultSort [_dv] = do
        _dv <- Builtin.expectDomainValue token2StringKey _dv
        return (asPattern resultSort _dv)
    evalToken2String0 _ _ _ = Builtin.wrongArity token2StringKey

evalString2Token :: BuiltinAndAxiomSimplifier
evalString2Token = Builtin.functionEvaluator evalString2Token0
  where
    evalString2Token0 _ resultSort [_str] = do
        _str <- expectBuiltinString string2TokenKey _str
        Builtin.makeDomainValuePattern resultSort _str
            & return
    evalString2Token0 _ _ _ = Builtin.wrongArity token2StringKey

-- | Implement builtin function evaluation.
builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == eqKey = Just $ comparator eqKey (==)
    | key == ltKey = Just $ comparator ltKey (<)
    | key == plusKey = Just $ binaryOperator plusKey Text.append
    | key == substrKey = Just evalSubstr
    | key == lengthKey = Just evalLength
    | key == findKey = Just evalFind
    | key == string2BaseKey = Just evalString2Base
    | key == base2StringKey = Just evalBase2String
    | key == string2IntKey = Just evalString2Int
    | key == int2StringKey = Just evalInt2String
    | key == chrKey = Just evalChr
    | key == ordKey = Just evalOrd
    | key == token2StringKey = Just evalToken2String
    | key == string2TokenKey = Just evalString2Token
    | otherwise = Nothing
  where
    comparator name op =
        Builtin.binaryOperator
            extractStringDomainValue
            Bool.asPattern
            name
            op
    binaryOperator name op =
        Builtin.binaryOperator
            extractStringDomainValue
            asPattern
            name
            op

data UnifyString = UnifyString
    { string1, string2 :: !InternalString
    , term1, term2 :: !(TermLike RewritingVariableName)
    }

{- | Matches

@
\\equals{_, _}(\\dv{String}(_), \\dv{String}(_))
@

and

@
\\and{_}(\\dv{String}(_), \\dv{String}}(_))
@
-}
matchString ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyString
matchString term1 term2
    | InternalString_ string1 <- term1
      , InternalString_ string2 <- term2 =
        Just UnifyString{string1, string2, term1, term2}
    | otherwise = Nothing
{-# INLINE matchString #-}

-- | Unification of String values.
unifyString ::
    forall unifier.
    MonadUnify unifier =>
    UnifyString ->
    unifier (Pattern RewritingVariableName)
unifyString unifyData =
    assert (on (==) internalStringSort string1 string2) worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
        | on (==) internalStringValue string1 string2 =
            return $ Pattern.fromTermLike term1
        | otherwise = debugUnifyBottomAndReturnBottom "distinct strings" term1 term2
    UnifyString{string1, string2, term1, term2} = unifyData

{- | Matches

@
\\equals{_, _}(\\dv{Bool}(_), eqString{_}(_,_)),
@

symmetric in the two arguments.
-}
matchUnifyStringEq ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEq
matchUnifyStringEq = Builtin.matchUnifyEq eqKey
{-# INLINE matchUnifyStringEq #-}
