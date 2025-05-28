{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Built-in functions (hooks) in the BYTES namespace, as described in
[docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).

* Only selected hooks are implemented.
* Depends on the Int and Bool built-in types.
* String conversions are _not_ implemented (there is no internalised string type)
-}
module Booster.Builtin.BYTES (
    builtinsBYTES,
    pattern BytesDV,
) where

import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Char (chr, ord)
import Data.Map (Map)
import Data.Map qualified as Map

import Booster.Builtin.Base
import Booster.Builtin.INT (intTerm', readIntTerm')
import Booster.Pattern.Base

builtinsBYTES :: Map ByteString BuiltinFunction
builtinsBYTES =
    Map.mapKeys ("BYTES." <>) $
        Map.fromList
            [ "update" ~~> bytesupdateHook
            , "get" ~~> bytesgetHook
            , "substr" ~~> bytessubstrHook
            , "replaceAt" ~~> bytesreplaceAtHook
            , "padRight" ~~> bytespadRightHook
            , "padLeft" ~~> bytespadLeftHook
            , "reverse" ~~> bytesreverseHook
            , "length" ~~> byteslengthHook
            , "concat" ~~> bytesconcatHook
            , "int2bytes" ~~> bytesint2bytesHook
            , "bytes2int" ~~> bytesbytes2intHook
            ]

bytesupdateHook
    , bytesgetHook
    , bytessubstrHook
    , bytesreplaceAtHook
    , bytespadRightHook
    , bytespadLeftHook
    , bytesreverseHook
    , byteslengthHook
    , bytesconcatHook
    , bytesint2bytesHook
    , bytesbytes2intHook ::
        BuiltinFunction

-- | in 'bytes', replace element at 'idx' (valid index) by 'new' (within 0..255)
bytesupdateHook [bytes, idx, new]
    | BytesDV bs <- bytes
    , Just i <- readIntTerm' idx
    , 0 <= i && i < BS.length bs
    , Just d <- readIntTerm' new
    , 0 <= d && d <= 255 = do
        let (front, rest) = BS.splitAt i bs
            -- NB back not empty because i < length bytes
            back = BS.tail rest
        pure $ Just $ BytesDV $ front <> BS.cons (chr d) back
bytesupdateHook other = arityError "BYTES.update" 3 other

-- | read int at index 'idx' from bytes ('idx' non-negative and < length bytes)
bytesgetHook [bytes, idx]
    | BytesDV bs <- bytes
    , Just i <- readIntTerm' idx
    , 0 <= i && i < BS.length bs =
        pure $ Just $ intTerm' $ ord $ BS.index bs i
bytesgetHook other = arityError "BYTES.get" 2 other

{- | extract a sub-sequence [start .. end) from the bytes
  * 'start' must be non-negative and < length bytes
  * 'end' must be >='start' and <= length bytes
-}
bytessubstrHook [bytes, start, end]
    | BytesDV bs <- bytes
    , Just st <- readIntTerm' start
    , 0 <= st && st < BS.length bs
    , Just e <- readIntTerm' end
    , st <= e && e <= BS.length bs = do
        let left = BS.take e bs -- st <= e, therefore st <= length left
        pure $ Just $ BytesDV $ BS.drop st left
bytessubstrHook other = arityError "BYTES.substr" 3 other

-- | what exactly is the semantics?
bytesreplaceAtHook other = arityError "BYTES.replaceAt" 3 other

-- | pad a byte array on the right with 'pad' to have at least length 'len'
bytespadRightHook [bytes, len, pad]
    | BytesDV bs <- bytes
    , Just l <- readIntTerm' len
    , Just p <- chr <$> readIntTerm' pad =
        if BS.length bs >= l
            then pure $ Just bytes
            else pure $ Just $ BytesDV $ bs <> BS.replicate (l - BS.length bs) p
bytespadRightHook other = arityError "BYTES.padRight" 3 other

-- | pad a byte array on the left with 'pad' to have at least length 'len'
bytespadLeftHook [bytes, len, pad]
    | BytesDV bs <- bytes
    , Just l <- readIntTerm' len
    , Just p <- chr <$> readIntTerm' pad =
        if BS.length bs >= l
            then pure $ Just bytes
            else pure $ Just $ BytesDV $ BS.replicate (l - BS.length bs) p <> bs
bytespadLeftHook other = arityError "BYTES.padLeft" 3 other

-- | reverse the bytes in a byte array
bytesreverseHook [BytesDV bs] = pure . Just . BytesDV $ BS.reverse bs
bytesreverseHook other = arityError "BYTES.reverse" 1 other

-- | length of a byte array
byteslengthHook [BytesDV bs] = pure . Just . intTerm' $ BS.length bs
byteslengthHook other = arityError "BYTES.length" 1 other

-- | concatenate two byte arrays
bytesconcatHook [BytesDV bs1, BytesDV bs2] = pure . Just . BytesDV $ bs1 <> bs2
bytesconcatHook other = arityError "BYTES.concat" 2 other

bytesint2bytesHook other = arityError "BYTES.int2bytes" 3 other
bytesbytes2intHook other = arityError "BYTES.bytes2int" 3 other

------------------------

pattern BytesDV :: ByteString -> Term
pattern BytesDV bs = DomainValue SortBytes bs
