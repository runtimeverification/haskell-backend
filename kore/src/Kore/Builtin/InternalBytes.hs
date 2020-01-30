{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}

module Kore.Builtin.InternalBytes
    ( sort
    , assertSort
    , verifiers
    , builtinFunctions
    , asInternal
    , internalize
    , asTermLike
    , asPattern
      -- * Keys
    , bytes2StringKey
    , string2BytesKey
    , updateKey
    , getKey
    , substrKey
    , replaceAtKey
    , padRightKey
    , padLeftKey
    , reverseKey
    , lengthKey
    , concatKey
    ) where

import Prelude.Kore

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT
    )
import qualified Control.Monad as Monad
import Data.ByteString
    ( ByteString
    )
import qualified Data.ByteString as ByteString
import Data.Functor.Const
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )
import Data.Word
    ( Word8
    )

import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Encoding as Encoding
import Kore.Builtin.Endianness.Endianness
import qualified Kore.Builtin.Int as Int
import Kore.Builtin.InternalBytes.InternalBytes
import Kore.Builtin.Signedness.Signedness
import qualified Kore.Builtin.String as String
import qualified Kore.Error
import Kore.Internal.ApplicationSorts
    ( applicationSortsResult
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
    ( symbolSorts
    )
import Kore.Internal.TermLike
import qualified Kore.Verified as Verified

-- | Verify that the sort is hooked to the @Bytes@ sort.
-- | See also: 'sort', 'Builtin.verifySort'.
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook
        }

-- | Verify that hooked sort declarations are well-formed.
-- | See also: 'Builtin.verifySortDecl'.
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

-- | Verify that hooked symbol declarations are well-formed.
-- | See also: 'Builtin.verifySymbol'.
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [   ( bytes2StringKey
        , Builtin.verifySymbol string [bytes]
        )
    ,   ( string2BytesKey
        , Builtin.verifySymbol bytes [string]
        )
    ,   ( updateKey
        , Builtin.verifySymbol bytes [bytes, int, int]
        )
    ,   ( getKey
        , Builtin.verifySymbol int [bytes, int]
        )
    ,   ( substrKey
        , Builtin.verifySymbol bytes [bytes, int, int]
        )
    ,   ( replaceAtKey
        , Builtin.verifySymbol bytes [bytes, int, bytes]
        )
    ,   ( padRightKey
        , Builtin.verifySymbol bytes [bytes, int, int]
        )
    ,   ( padLeftKey
        , Builtin.verifySymbol bytes [bytes, int, int]
        )
    ,   ( reverseKey
        , Builtin.verifySymbol bytes [bytes]
        )
    ,   ( lengthKey
        , Builtin.verifySymbol int [bytes]
        )
    ,   ( concatKey
        , Builtin.verifySymbol bytes [bytes, bytes]
        )
    ,   ( int2bytesKey
        , Builtin.verifySymbol bytes [int, int, anySort]
        )
    ,   ( bytes2intKey
        , Builtin.verifySymbol int [bytes, anySort, anySort]
        )
    ]
  where
    bytes   = assertSort
    int     = Int.assertSort
    string  = String.assertSort
    anySort = Builtin.acceptAnySort

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifierHook :: Builtin.PatternVerifierHook
patternVerifierHook =
    Builtin.domainValuePatternVerifierHook sort patternVerifierWorker
    <> (Builtin.applicationPatternVerifierHooks . HashMap.fromList)
        [ (Builtin.HookedSymbolKey dotBytes, dotBytesVerifier ) ]
  where
    patternVerifierWorker external =
        case externalChild of
            StringLiteral_ literal -> do
                bytesValue <- Builtin.parseString Encoding.parseBase16 literal
                (return . InternalBytesF . Const)
                    InternalBytes { bytesSort, bytesValue }
            _ -> Kore.Error.koreFail "Expected literal string"
      where
        DomainValue { domainValueSort = bytesSort } = external
        DomainValue { domainValueChild = externalChild } = external

dotBytes :: IsString str => str
dotBytes = "BYTES.empty"

dotBytesVerifier
    :: Builtin.ApplicationVerifier Verified.Pattern
dotBytesVerifier =
    Builtin.ApplicationVerifier worker
  where
    worker application = do
        Monad.unless (null arguments)
            (Kore.Error.koreFail "expected zero arguments")
        (return . InternalBytesF . Const)
            InternalBytes { bytesSort, bytesValue = Encoding.encode8Bit "" }
      where
        arguments = applicationChildren application
        symbol = applicationSymbolOrAlias application
        bytesSort = applicationSortsResult . symbolSorts $ symbol

matchBuiltinBytes :: Monad m => TermLike variable -> MaybeT m ByteString
matchBuiltinBytes (InternalBytes_ _ byteString) = return byteString
matchBuiltinBytes _ = empty

evalBytes2String :: Builtin.Function
evalBytes2String =
    Builtin.functionEvaluator evalBytes2String0
  where
    evalBytes2String0 :: Builtin.FunctionImplementation
    evalBytes2String0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let _bytes =
                    case arguments of
                        [_bytes] -> _bytes
                        _ -> Builtin.wrongArity bytes2StringKey
            bytestring <- matchBuiltinBytes _bytes
            Builtin.appliedFunction
                . String.asPattern resultSort
                . Encoding.decode8Bit
                $ bytestring

evalString2Bytes :: Builtin.Function
evalString2Bytes =
    Builtin.functionEvaluator evalString2Bytes0
  where
    evalString2Bytes0 :: Builtin.FunctionImplementation
    evalString2Bytes0 resultSort [_string] =
        Builtin.getAttemptedAxiom $ do
            _string <- String.expectBuiltinString string2BytesKey _string
            Builtin.appliedFunction . asPattern resultSort
                $ Encoding.encode8Bit _string
    evalString2Bytes0 _ _ = Builtin.wrongArity string2BytesKey

evalUpdate :: Builtin.Function
evalUpdate =
    Builtin.functionEvaluator evalUpdate0
  where
    evalUpdate0 :: Builtin.FunctionImplementation
    evalUpdate0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_bytes, _index, _value) =
                    case arguments of
                        [_bytes, _index, _value] -> (_bytes, _index, _value)
                        _ -> Builtin.wrongArity updateKey
            _bytes <- matchBuiltinBytes _bytes
            _index <- fromInteger <$> Int.expectBuiltinInt updateKey _index
            _value <- fromInteger <$> Int.expectBuiltinInt updateKey _value
            if _index < 0 || _index > (ByteString.length _bytes - 1)
                then Builtin.appliedFunction Pattern.bottom
                else
                    Builtin.appliedFunction . asPattern resultSort
                        $ ByteString.take _index _bytes
                            <> ByteString.singleton _value
                            <> ByteString.drop (_index + 1) _bytes

evalGet :: Builtin.Function
evalGet =
    Builtin.functionEvaluator evalGet0
  where
    evalGet0 :: Builtin.FunctionImplementation
    evalGet0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_bytes, _index) =
                    case arguments of
                        [_bytes, _index] -> (_bytes, _index)
                        _ -> Builtin.wrongArity getKey
            _bytes <- matchBuiltinBytes _bytes
            _index <- fromInteger <$> Int.expectBuiltinInt getKey _index
            if _index >= ByteString.length _bytes || _index < 0
                then Builtin.appliedFunction Pattern.bottom
                else
                    Builtin.appliedFunction
                        . Int.asPattern resultSort
                        . toInteger
                        $ ByteString.index _bytes _index

evalSubstr :: Builtin.Function
evalSubstr =
    Builtin.functionEvaluator evalSubstr0
  where
    evalSubstr0 :: Builtin.FunctionImplementation
    evalSubstr0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_bytes, _start, _end) =
                    case arguments of
                        [_bytes, _start, _end] -> (_bytes, _start, _end)
                        _ -> Builtin.wrongArity substrKey
            _bytes <- matchBuiltinBytes _bytes
            _start <- fromInteger <$> Int.expectBuiltinInt substrKey _start
            _end   <- fromInteger <$> Int.expectBuiltinInt substrKey _end
            let outOfBounds =
                       (_start < 0)
                    || (_end > ByteString.length _bytes)
                    || (_end - _start < 0)
            if outOfBounds
                then Builtin.appliedFunction Pattern.bottom
                else
                    Builtin.appliedFunction . asPattern resultSort
                        $ ByteString.take (_end - _start)
                        . ByteString.drop _start
                        $ _bytes

evalReplaceAt :: Builtin.Function
evalReplaceAt =
    Builtin.functionEvaluator evalReplaceAt0
  where
    evalReplaceAt0 :: Builtin.FunctionImplementation
    evalReplaceAt0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_bytes, _index, _new) =
                    case arguments of
                        [_bytes, _index, _new] -> (_bytes, _index, _new)
                        _ -> Builtin.wrongArity replaceAtKey
            _bytes <- matchBuiltinBytes _bytes
            _index <- fromInteger <$> Int.expectBuiltinInt replaceAtKey _index
            _new   <- matchBuiltinBytes _new
            Builtin.appliedFunction
                . maybe Pattern.bottom (asPattern resultSort)
                $ go _bytes _index _new

    go _bytes _index _new
      | ByteString.length _new == 0 = Just _bytes
      | _index >= ByteString.length _bytes = Nothing
      | _index < 0 = Nothing
      | ByteString.length _bytes == 0 = Nothing
      | otherwise = Just $ ByteString.take _index _bytes
                            <> _new
                            <> ByteString.drop (_index + ByteString.length _new) _bytes

evalPadRight :: Builtin.Function
evalPadRight =
    Builtin.functionEvaluator evalPadRight0
  where
    evalPadRight0 :: Builtin.FunctionImplementation
    evalPadRight0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_bytes, _length, _value) =
                    case arguments of
                        [_bytes, _length, _value] -> (_bytes, _length, _value)
                        _ -> Builtin.wrongArity padRightKey
            _bytes  <- matchBuiltinBytes _bytes
            _length <- fromInteger <$> Int.expectBuiltinInt padRightKey _length
            _value  <- fromInteger <$> Int.expectBuiltinInt padRightKey _value
            Builtin.appliedFunction $ go resultSort _bytes _length _value

    go resultSort bytes len val
      | len <= ByteString.length bytes = asPattern resultSort bytes
      | otherwise =
        asPattern resultSort
            $ bytes <> ByteString.replicate (len - ByteString.length bytes) val

evalPadLeft :: Builtin.Function
evalPadLeft =
    Builtin.functionEvaluator evalPadLeft0
  where
    evalPadLeft0 :: Builtin.FunctionImplementation
    evalPadLeft0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_bytes, _length, _value) =
                    case arguments of
                        [_bytes, _length, _value] -> (_bytes, _length, _value)
                        _ -> Builtin.wrongArity padLeftKey
            _bytes  <- matchBuiltinBytes _bytes
            _length <- fromInteger <$> Int.expectBuiltinInt padLeftKey _length
            _value  <- fromInteger <$> Int.expectBuiltinInt padLeftKey _value
            Builtin.appliedFunction $ go resultSort _bytes _length _value

    go resultSort bytes len val
      | len <= ByteString.length bytes = asPattern resultSort bytes
      | otherwise =
        asPattern resultSort
            $ ByteString.replicate (len - ByteString.length bytes) val <> bytes

evalReverse :: Builtin.Function
evalReverse =
    Builtin.functionEvaluator evalReverse0
  where
    evalReverse0 :: Builtin.FunctionImplementation
    evalReverse0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let _bytes =
                    case arguments of
                        [_bytes] -> _bytes
                        _ -> Builtin.wrongArity reverseKey
            _bytes  <- matchBuiltinBytes _bytes
            Builtin.appliedFunction . asPattern resultSort
                $ ByteString.reverse _bytes

evalLength :: Builtin.Function
evalLength =
    Builtin.functionEvaluator evalLength0
  where
    evalLength0 :: Builtin.FunctionImplementation
    evalLength0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let _bytes =
                    case arguments of
                        [_bytes] -> _bytes
                        _ -> Builtin.wrongArity lengthKey
            _bytes  <- matchBuiltinBytes _bytes
            Builtin.appliedFunction
                . Int.asPattern resultSort
                . toInteger
                $ ByteString.length _bytes

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0 :: Builtin.FunctionImplementation
    evalConcat0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_lhs, _rhs) =
                    case arguments of
                        [_lhs, _rhs] -> (_lhs, _rhs)
                        _ -> Builtin.wrongArity concatKey
            _lhs  <- matchBuiltinBytes _lhs
            _rhs  <- matchBuiltinBytes _rhs
            Builtin.appliedFunction . asPattern resultSort $ _lhs <> _rhs

evalInt2bytes :: Builtin.Function
evalInt2bytes =
    Builtin.functionEvaluator evalInt2bytes0
  where
    evalInt2bytes0 :: Builtin.FunctionImplementation
    evalInt2bytes0 resultSort [len, int, end] =
        Builtin.getAttemptedAxiom $ do
            end' <-
                case end of
                    Endianness_ endianness -> return endianness
                    _                      -> empty
            len' <- Int.expectBuiltinInt int2bytesKey len
            int' <- Int.expectBuiltinInt int2bytesKey int
            let result = int2bytes (fromInteger len') int' end'
            Builtin.appliedFunction $ asPattern resultSort result
    evalInt2bytes0 _ _ = Builtin.wrongArity int2bytesKey

int2bytes :: Int -> Integer -> Endianness -> ByteString
int2bytes len int end =
    case end of
        LittleEndian _ -> littleEndian
        BigEndian    _ -> ByteString.reverse littleEndian
  where
    (littleEndian, _) = ByteString.unfoldrN len go int
    go int'
      | int' == 0 = Just (pad, 0)
      | otherwise = let (d, m) = divMod int' 0x100 in Just (word8 m, d)
    pad
      | int < 0   = 0xFF
      | otherwise = 0x00

    word8 :: Integer -> Word8
    word8 = toEnum . fromEnum

evalBytes2int :: Builtin.Function
evalBytes2int =
    Builtin.functionEvaluator evalBytes2int0
  where
    evalBytes2int0 :: Builtin.FunctionImplementation
    evalBytes2int0 resultSort [bytes, end, sign] =
        Builtin.getAttemptedAxiom $ do
            end' <-
                case end of
                    Endianness_ endianness -> return endianness
                    _                      -> empty
            sign' <-
                case sign of
                    Signedness_ signedness -> return signedness
                    _                      -> empty
            bytes' <- matchBuiltinBytes bytes
            let result = bytes2int bytes' end' sign'
            Builtin.appliedFunction $ Int.asPattern resultSort result
    evalBytes2int0 _ _ = Builtin.wrongArity bytes2intKey

bytes2int :: ByteString -> Endianness -> Signedness -> Integer
bytes2int bytes end sign =
    case sign of
        Unsigned _ -> unsigned
        Signed   _
          | 2 * unsigned > modulus -> unsigned - modulus
          | otherwise              -> unsigned
  where
    (modulus, unsigned) = ByteString.foldl' go (1, 0) littleEndian
    go (!place, !acc) byte =
        let !place' = place * 0x100
            !acc' = acc + place * fromIntegral byte
        in (place', acc')
    littleEndian =
        case end of
            LittleEndian _ -> bytes
            BigEndian    _ -> ByteString.reverse bytes

builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (bytes2StringKey, evalBytes2String)
        , (string2BytesKey, evalString2Bytes)
        , (updateKey, evalUpdate)
        , (getKey, evalGet)
        , (substrKey, evalSubstr)
        , (replaceAtKey, evalReplaceAt)
        , (padRightKey, evalPadRight)
        , (padLeftKey, evalPadLeft)
        , (reverseKey, evalReverse)
        , (lengthKey, evalLength)
        , (concatKey, evalConcat)
        , (int2bytesKey, evalInt2bytes)
        , (bytes2intKey, evalBytes2int)
        ]
