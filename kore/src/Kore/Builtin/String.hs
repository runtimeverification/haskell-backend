{- |
Module      : Kore.Builtin.String
Description : Built-in string sort
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.String as String
@
 -}

module Kore.Builtin.String
    ( sort
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , patternVerifier
    , builtinFunctions
    , expectBuiltinString
    , asInternal
    , asPattern
    , asTermLike
    , asPartialPattern
    , parse
      -- * keys
    , ltKey
    , plusKey
    , string2IntKey
    , substrKey
    , lengthKey
    , findKey
    , string2BaseKey
    , chrKey
    , ordKey
    , token2StringKey
    , string2TokenKey
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT
    )
import Data.Char
    ( chr
    , ord
    )
import qualified Data.HashMap.Strict as HashMap
import Data.List
    ( findIndex
    )
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Data.Text.Read as Text
import Numeric
    ( readOct
    )
import qualified Text.Megaparsec as Parsec

import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import Kore.Builtin.String.String
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike as TermLike


{- | Verify that the sort is hooked to the builtin @String@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [   ( ltKey
        , Builtin.verifySymbol Bool.assertSort [assertSort, assertSort]
        )
    ,   ( plusKey
        , Builtin.verifySymbol assertSort [assertSort, assertSort]
        )
    ,   ( substrKey
        , Builtin.verifySymbol
            assertSort
            [assertSort, Int.assertSort, Int.assertSort]
        )
    ,   ( lengthKey
        , Builtin.verifySymbol Int.assertSort [assertSort]
        )
    ,   ( findKey
        , Builtin.verifySymbol
            Int.assertSort
            [assertSort, assertSort, Int.assertSort]
        )
    ,   ( string2BaseKey
        , Builtin.verifySymbol
            Int.assertSort
            [assertSort, Int.assertSort]
        )
    ,   ( string2IntKey
        , Builtin.verifySymbol Int.assertSort [assertSort]
        )
    ,   ( chrKey
        , Builtin.verifySymbol assertSort [Int.assertSort]
        )
    ,   ( ordKey
        , Builtin.verifySymbol Int.assertSort [assertSort]
        )
    ,   ( token2StringKey
        , Builtin.verifySymbol
            assertSort
            [Builtin.verifySortHasDomainValues]
        )
    ,   ( string2TokenKey
        , Builtin.verifySymbol
            Builtin.verifySortHasDomainValues
            [assertSort]
        )
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifier :: Builtin.DomainValueVerifier (TermLike variable)
patternVerifier =
    Builtin.makeEncodedDomainValueVerifier sort patternVerifierWorker
  where
    patternVerifierWorker domainValue =
        case externalChild of
            StringLiteral_ internalStringValue ->
                (return . Domain.BuiltinString)
                    Domain.InternalString
                        { internalStringSort
                        , internalStringValue
                        }
            _ -> Kore.Error.koreFail "Expected literal string"
      where
        DomainValue { domainValueSort = internalStringSort } = domainValue
        DomainValue { domainValueChild = externalChild } = domainValue

-- | get the value from a (possibly encoded) domain value
extractStringDomainValue
    :: Text -- ^ error message Context
    -> Builtin (TermLike variable)
    -> Text
extractStringDomainValue ctx =
    \case
        Domain.BuiltinString internal ->
            internalStringValue
          where
            Domain.InternalString { internalStringValue } = internal
        _ ->
            Builtin.verifierBug
            $ Text.unpack ctx ++ ": Domain value is not a string"

{- | Parse a string literal.
 -}
parse :: Builtin.Parser Text
parse = Text.pack <$> Parsec.many Parsec.anySingle

{- | Abort function evaluation if the argument is not a String domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinString
    :: Monad m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m Text
expectBuiltinString ctx =
    \case
        Builtin_ domain ->
            case domain of
                Domain.BuiltinString internal ->
                    return internalStringValue
                  where
                    Domain.InternalString { internalStringValue } = internal
                _ ->
                    Builtin.verifierBug
                    $ Text.unpack ctx ++ ": Domain value is not a string"
        _ -> empty


evalSubstr :: Builtin.Function
evalSubstr = Builtin.functionEvaluator evalSubstr0
  where
    substr :: Int -> Int -> Text -> Text
    substr startIndex endIndex =
        Text.take (endIndex - startIndex) . Text.drop startIndex
    evalSubstr0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let (_str, _start, _end) =
                    case arguments of
                        [_str, _start, _end] -> (_str, _start, _end)
                        _                    -> Builtin.wrongArity substrKey
            _str   <- expectBuiltinString substrKey _str
            _start <- fromInteger <$> Int.expectBuiltinInt substrKey _start
            _end   <- fromInteger <$> Int.expectBuiltinInt substrKey _end
            Builtin.appliedFunction
                . asPattern resultSort
                $ substr _start _end _str

evalLength :: Builtin.Function
evalLength = Builtin.functionEvaluator evalLength0
  where
    evalLength0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _str =
                    case arguments of
                        [_str] -> _str
                        _      -> Builtin.wrongArity lengthKey
            _str <- expectBuiltinString lengthKey _str
            Builtin.appliedFunction
                . Int.asPattern resultSort
                . toInteger
                $ Text.length _str

evalFind :: Builtin.Function
evalFind = Builtin.functionEvaluator evalFind0
  where
    maybeNotFound :: Maybe Int -> Integer
    maybeNotFound = maybe (-1) toInteger
    evalFind0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let (_str, _substr, _idx) =
                    case arguments of
                        [_str, _substr, _idx] -> (_str, _substr, _idx)
                        _                     -> Builtin.wrongArity findKey
            _str <- expectBuiltinString findKey _str
            _substr <- expectBuiltinString findKey _substr
            _idx <- fromInteger <$> Int.expectBuiltinInt substrKey _idx
            Builtin.appliedFunction
                . Int.asPattern resultSort
                . maybeNotFound
                $ findIndex
                    (Text.isPrefixOf _substr)
                    (Text.tails . Text.drop _idx $ _str)

evalString2Base :: Builtin.Function
evalString2Base = Builtin.functionEvaluator evalString2Base0
  where
    evalString2Base0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let (_str, _base) =
                    case arguments of
                        [_str, _base] -> (_str, _base)
                        _             -> Builtin.wrongArity string2BaseKey
            _str  <- expectBuiltinString string2BaseKey _str
            _base <- Int.expectBuiltinInt string2BaseKey _base
            let readN =
                    case _base of
                        -- no builtin reader for number in octal notation
                        8  -> \s ->
                            case readOct $ Text.unpack s of
                                [(result, "")] -> Right (result, "")
                                _              -> Left ""
                        10 -> Text.signed Text.decimal
                        16 -> Text.hexadecimal
                        _  -> const empty
            case readN _str of
                Right (result, Text.unpack -> "") ->
                    Builtin.appliedFunction
                        . Int.asPattern resultSort
                        $ result
                _ ->
                    Builtin.appliedFunction Pattern.bottom

evalString2Int :: Builtin.Function
evalString2Int = Builtin.functionEvaluator evalString2Int0
  where
    evalString2Int0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _str =
                    case arguments of
                        [_str] -> _str
                        _      -> Builtin.wrongArity string2IntKey
            _str <- expectBuiltinString string2IntKey _str
            case Text.signed Text.decimal _str of
                Right (result, Text.unpack -> "") ->
                    Builtin.appliedFunction
                    . Int.asPattern resultSort
                    $ result
                _ ->
                    Builtin.appliedFunction Pattern.bottom

evalChr :: Builtin.Function
evalChr = Builtin.functionEvaluator evalChr0
  where
    evalChr0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _n =
                    case arguments of
                        [_n] -> _n
                        _    -> Builtin.wrongArity chrKey
            _n <- Int.expectBuiltinInt chrKey _n
            Builtin.appliedFunction
                . asPattern resultSort
                $ Text.singleton $ chr $ fromIntegral _n

evalOrd :: Builtin.Function
evalOrd = Builtin.functionEvaluator evalOrd0
  where
    evalOrd0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _str =
                    case arguments of
                        [_str] -> _str
                        _    -> Builtin.wrongArity ordKey
            _str <- expectBuiltinString ordKey _str
            Builtin.appliedFunction
                . maybe Pattern.bottom charToOrdInt
                $ if Text.length _str == 1
                      then Just (Text.head _str)
                      else Nothing
      where
        charToOrdInt =
            Int.asPattern resultSort
            . toInteger
            . ord

evalToken2String :: Builtin.Function
evalToken2String = Builtin.functionEvaluator evalToken2String0
  where
      evalToken2String0 _ resultSort arguments =
          Builtin.getAttemptedAxiom $ do
              let _dv =
                      case arguments of
                          [_dv] -> _dv
                          _     -> Builtin.wrongArity token2StringKey
              _dv <- Builtin.expectDomainValue token2StringKey _dv
              Builtin.appliedFunction . asPattern resultSort $ _dv

evalString2Token :: Builtin.Function
evalString2Token = Builtin.functionEvaluator evalString2Token0
  where
      evalString2Token0 _ resultSort arguments =
          Builtin.getAttemptedAxiom $ do
              let _str =
                      case arguments of
                          [_str] -> _str
                          _     -> Builtin.wrongArity token2StringKey
              _str <- expectBuiltinString string2TokenKey _str
              Builtin.appliedFunction
                 $ Builtin.makeDomainValuePattern
                    resultSort
                    _str

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
    [ comparator ltKey (<)
    , binaryOperator plusKey Text.append
    , (substrKey, evalSubstr)
    , (lengthKey, evalLength)
    , (findKey, evalFind)
    , (string2BaseKey, evalString2Base)
    , (string2IntKey, evalString2Int)
    , (chrKey, evalChr)
    , (ordKey, evalOrd)
    , (token2StringKey, evalToken2String)
    , (string2TokenKey, evalString2Token)
    ]
  where
    comparator name op =
        ( name, Builtin.binaryOperator extractStringDomainValue
            Bool.asPattern name op )
    binaryOperator name op =
        ( name, Builtin.binaryOperator extractStringDomainValue
            asPattern name op )
