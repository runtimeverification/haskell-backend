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
import Booster.Builtin.INT (intTerm, intTerm', readIntTerm, readIntTerm')
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

{- | Insert the given 'new' byte string into the given 'bytes' array at
  index 'idx'. This may make the 'bytes' longer than before if 'new'
  is inserted near the end of 'bytes'.
  Undefined (Nothing) for invalid 'idx' (not in range '[0..length bytes)',
  or if 'bytes' is empty (which makes _any_ 'idx' invalid).
-}
bytesreplaceAtHook [bytes, idx, replace]
    | BytesDV new <- replace
    , BS.null new =
        pure $ Just bytes
    | BytesDV new <- replace
    , BytesDV bs <- bytes
    , Just i <- readIntTerm' idx
    , 0 <= i && i < BS.length bs = do
        let (front, target) = BS.splitAt i bs
            (_, back) = BS.splitAt (BS.length new) target
        pure . Just . BytesDV $ front <> new <> back
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

{- | return byte representation of the given 'value::Integer',
   left-padded to the given 'maxLen' in bytes, with given 'endianness'.
   If 'maxLen' is smaller than the bytes required to represent 'value',
   then the most significant bytes will be _truncated_.
-}
bytesint2bytesHook [maxLen, value, endianness]
    | Just len <- readIntTerm' maxLen
    , Just val <- readIntTerm value
    , Just end <- readEndianness endianness =
        pure . Just . BytesDV $
            (if end == LittleEndian then id else BS.reverse) $
                int2bytes len val
bytesint2bytesHook other = arityError "BYTES.int2bytes" 3 other

{- | interpret given 'bytes' as an unsigned or 2s-complement number,
   with the given 'endianness'
-}
bytesbytes2intHook [bytes, endianness, signedness]
    | BytesDV bs <- bytes
    , Just end <- readEndianness endianness
    , Just sign <- readSignedness signedness =
        pure . Just . intTerm $
            bytes2int sign $
                if end == LittleEndian then bs else BS.reverse bs
bytesbytes2intHook other = arityError "BYTES.bytes2int" 3 other

------------------------

{- | return little-endian bytes for given (signed) number,
  padded/truncated to length
-}
int2bytes :: Int -> Integer -> ByteString
int2bytes maxLength number = fst $ BS.unfoldrN maxLength go number
  where
    go n
        | n == 0 = Just (pad, 0)
        | otherwise = let (d, m) = divMod n 0x100 in Just (chr $ fromIntegral m, d)
    pad = if number < 0 then '\255' else '\0'

-- | interprets bytes as a little-endian 2s-complement or unsigned integer
bytes2int :: Signedness -> ByteString -> Integer
bytes2int signedness bytes =
    case signedness of
        Unsigned -> unsigned
        Signed
            | 2 * unsigned >= modulus -> unsigned - modulus
            | otherwise -> unsigned
  where
    (modulus, unsigned) = BS.foldl' times256 (1, 0) bytes
    times256 (place, acc) c =
        let !place' = place * 0x100
            !acc' = acc + place * fromIntegral (ord c)
         in (place', acc')

data Endianness
    = LittleEndian
    | BigEndian
    deriving (Eq, Show)

readEndianness :: Term -> Maybe Endianness
readEndianness = \case
    DomainValue SortEndianness "littleEndianBytes" -> Just LittleEndian
    DomainValue SortEndianness "bigEndianBytes" -> Just BigEndian
    _other -> Nothing

pattern SortEndianness :: Sort
pattern SortEndianness = SortApp "SortEndianness" []

data Signedness
    = Signed
    | Unsigned
    deriving (Eq, Show)

readSignedness :: Term -> Maybe Signedness
readSignedness = \case
    DomainValue SortSignedness "signedBytes" -> Just Signed
    DomainValue SortSignedness "unsignedBytes" -> Just Unsigned
    _other -> Nothing

pattern SortSignedness :: Sort
pattern SortSignedness = SortApp "SortSignedness" []

pattern BytesDV :: ByteString -> Term
pattern BytesDV bs = DomainValue SortBytes bs
