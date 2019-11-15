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

import Control.Error
    ( MaybeT
    )
import Data.ByteString
    ( ByteString
    )
import qualified Data.ByteString as BS
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Encoding as E
import qualified Kore.Builtin.Int as Int
import Kore.Builtin.InternalBytes.InternalBytes
import qualified Kore.Builtin.String as String
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify

-- | Verify that the sort is hooked to the @Bytes@ sort.
-- | See also: 'sort', 'Builtin.verifySort'.
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , domainValueVerifiers = mempty
        , applicationVerifiers = mempty
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
    ]
  where
    bytes  = assertSort
    int    = Int.assertSort
    string = String.assertSort

expectBuiltinBytes
    :: MonadSimplify m
    => Text
    -> TermLike variable
    -> MaybeT m (Symbol, ByteString)
expectBuiltinBytes ctx =
    \case
        InternalBytes_ _ symbol bytesValue -> return (symbol, bytesValue)
        _ ->
            Builtin.verifierBug
            $ Text.unpack ctx ++ ": Term not a bytes value"

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
            (_, bytestring) <- expectBuiltinBytes bytes2StringKey _bytes
            Builtin.appliedFunction
                . String.asPattern resultSort
                . E.decode8Bit
                $ bytestring

evalString2Bytes :: Builtin.Function
evalString2Bytes =
    applicationAxiomSimplifier evalString2Bytes0
  where
    evalString2Bytes0
        :: forall variable simplifier
        .  (SimplifierVariable variable, MonadSimplify simplifier)
        => CofreeF
            (Application Symbol)
            (Attribute.Pattern variable)
            (TermLike variable)
        -> simplifier (AttemptedAxiom variable)
    evalString2Bytes0 (attrs :< app) = Builtin.getAttemptedAxiom $ do
        let (symbol, _string) =
                case app of
                    Application
                        { applicationChildren = [_string]
                        , applicationSymbolOrAlias
                        } -> (applicationSymbolOrAlias, _string)
                    _ -> Builtin.wrongArity string2BytesKey
            Attribute.Pattern { patternSort } = attrs

        _string <- String.expectBuiltinString string2BytesKey _string

        Builtin.appliedFunction
            . asPattern patternSort symbol
            . E.encode8Bit
            $ _string

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
            (symbol, _bytes) <- expectBuiltinBytes updateKey _bytes
            _index <- fromInteger <$> Int.expectBuiltinInt updateKey _index
            _value <- fromInteger <$> Int.expectBuiltinInt updateKey _value
            if _index < 0 || _index > (BS.length _bytes - 1)
                then Builtin.appliedFunction Pattern.bottom
                else
                    Builtin.appliedFunction
                        . asPattern resultSort symbol
                        $ BS.take _index _bytes
                            <> BS.singleton _value
                            <> BS.drop (_index + 1) _bytes

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
            (_, _bytes) <- expectBuiltinBytes getKey _bytes
            _index <- fromInteger <$> Int.expectBuiltinInt getKey _index
            if _index >= BS.length _bytes || _index < 0
                then Builtin.appliedFunction Pattern.bottom
                else
                    Builtin.appliedFunction
                        . Int.asPattern resultSort
                        . toInteger
                        $ BS.index _bytes _index

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
            (symbol, _bytes) <- expectBuiltinBytes substrKey _bytes
            _start <- fromInteger <$> Int.expectBuiltinInt substrKey _start
            _end   <- fromInteger <$> Int.expectBuiltinInt substrKey _end
            if (_start < 0) || (_end > BS.length _bytes) || (_end - _start < 0)
                then Builtin.appliedFunction Pattern.bottom
                else
                    Builtin.appliedFunction
                        . asPattern resultSort symbol
                        . BS.take (_end - _start)
                        . BS.drop _start
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
            (symbol, _bytes) <- expectBuiltinBytes replaceAtKey _bytes
            _index <- fromInteger <$> Int.expectBuiltinInt replaceAtKey _index
            (_, _new)   <- expectBuiltinBytes replaceAtKey _new
            Builtin.appliedFunction
                . maybe Pattern.bottom (asPattern resultSort symbol)
                $ go _bytes _index _new

    go _bytes _index _new
      | BS.length _new == 0 = Just _bytes
      | _index >= BS.length _bytes = Nothing
      | _index < 0 = Nothing
      | BS.length _bytes == 0 = Nothing
      | otherwise = Just $ BS.take _index _bytes
                            <> _new
                            <> BS.drop (_index + BS.length _new) _bytes

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
            (symbol, _bytes)  <- expectBuiltinBytes padRightKey _bytes
            _length <- fromInteger <$> Int.expectBuiltinInt padRightKey _length
            _value  <- fromInteger <$> Int.expectBuiltinInt padRightKey _value
            Builtin.appliedFunction $ go symbol resultSort _bytes _length _value

    go symbol resultSort bytes len val
      | len <= BS.length bytes = asPattern resultSort symbol bytes
      | otherwise =
        asPattern resultSort symbol
            $ bytes <> BS.replicate (len - BS.length bytes) val

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
            (symbol, _bytes)  <- expectBuiltinBytes padLeftKey _bytes
            _length <- fromInteger <$> Int.expectBuiltinInt padLeftKey _length
            _value  <- fromInteger <$> Int.expectBuiltinInt padLeftKey _value
            Builtin.appliedFunction $ go symbol resultSort _bytes _length _value

    go symbol resultSort bytes len val
      | len <= BS.length bytes = asPattern resultSort symbol bytes
      | otherwise =
        asPattern resultSort symbol
            $ BS.replicate (len - BS.length bytes) val <> bytes

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
            (symbol, _bytes)  <- expectBuiltinBytes reverseKey _bytes
            Builtin.appliedFunction
                . asPattern resultSort symbol
                $ BS.reverse _bytes

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
            (_, _bytes)  <- expectBuiltinBytes lengthKey _bytes
            Builtin.appliedFunction
                . Int.asPattern resultSort
                . toInteger
                $ BS.length _bytes

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
            (symbol, _lhs)  <- expectBuiltinBytes concatKey _lhs
            (_, _rhs)  <- expectBuiltinBytes concatKey _rhs
            Builtin.appliedFunction
                . asPattern resultSort symbol
                $ _lhs <> _rhs

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
        ]
