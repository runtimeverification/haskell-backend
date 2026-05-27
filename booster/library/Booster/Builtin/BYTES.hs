{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Built-in functions (hooks) in the BYTES namespace, as described in
[docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).
-}
module Booster.Builtin.BYTES (
    builtinsBYTES,
    readBytesTerm,
    bytesTerm,
) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BS8
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Word (Word8)

import Booster.Builtin.Base
import Booster.Builtin.INT (intTerm, readIntTerm)
import Booster.Pattern.Base

builtinsBYTES :: Map ByteString BuiltinFunction
builtinsBYTES =
    Map.mapKeys ("BYTES." <>) $
        Map.fromList
            [ "empty" ~~> bytesEmpty
            , "concat" ~~> bytesConcat
            , "length" ~~> bytesLength
            , "reverse" ~~> bytesReverse
            , "update" ~~> bytesUpdate
            , "get" ~~> bytesGet
            , "substr" ~~> bytesSubstr
            , "replaceAt" ~~> bytesReplaceAt
            , "padLeft" ~~> bytesPadLeft
            , "padRight" ~~> bytesPadRight
            , "int2bytes" ~~> bytesInt2Bytes
            , "bytes2int" ~~> bytesBytes2Int
            ]

-- | .Bytes constant: empty byte string
bytesEmpty :: BuiltinFunction
bytesEmpty args
    | null args = pure . Just $ bytesTerm ""
    | otherwise = arityError "BYTES.empty" 0 args

-- | +Bytes: concatenate two byte strings
bytesConcat :: BuiltinFunction
bytesConcat args
    | length args /= 2 = arityError "BYTES.concat" 2 args
    | [arg1, arg2] <- args
    , Just bs1 <- readBytesTerm arg1
    , Just bs2 <- readBytesTerm arg2 =
        pure . Just . bytesTerm $ bs1 <> bs2
    | otherwise = pure Nothing

-- | lengthBytes(BS): length of byte string as an integer
bytesLength :: BuiltinFunction
bytesLength args
    | length args /= 1 = arityError "BYTES.length" 1 args
    | [arg] <- args
    , Just bs <- readBytesTerm arg =
        pure . Just . DomainValue SortInt . BS8.pack . show $ BS.length bs
    | otherwise = pure Nothing

-- | reverseBytes(BS): reverse the byte sequence
bytesReverse :: BuiltinFunction
bytesReverse args
    | length args /= 1 = arityError "BYTES.reverse" 1 args
    | [arg] <- args
    , Just bs <- readBytesTerm arg =
        pure . Just . bytesTerm $ BS.reverse bs
    | otherwise = pure Nothing

-- | update(BS, i, byte): set byte at index i (0-based); returns Nothing if out of range
bytesUpdate :: BuiltinFunction
bytesUpdate args
    | length args /= 3 = arityError "BYTES.update" 3 args
    | [bsArg, iArg, byteArg] <- args
    , Just bs <- readBytesTerm bsArg
    , Just i <- readIntTerm iArg
    , Just byte <- readFillByte byteArg
    , i >= 0
    , fromIntegral i < BS.length bs =
        let idx = fromIntegral i
         in pure . Just . bytesTerm $
                BS.take idx bs <> BS.singleton byte <> BS.drop (idx + 1) bs
    | otherwise = pure Nothing

-- | get(BS, i): byte at index i as an integer (0-based); returns Nothing if out of range
bytesGet :: BuiltinFunction
bytesGet args
    | length args /= 2 = arityError "BYTES.get" 2 args
    | [bsArg, iArg] <- args
    , Just bs <- readBytesTerm bsArg
    , Just i <- readIntTerm iArg
    , i >= 0
    , fromIntegral i < BS.length bs =
        pure . Just . intTerm . toInteger $ BS.index bs (fromIntegral i)
    | otherwise = pure Nothing

-- | substr(BS, start, end): bytes in [start, end); returns Nothing if indices out of range
bytesSubstr :: BuiltinFunction
bytesSubstr args
    | length args /= 3 = arityError "BYTES.substr" 3 args
    | [bsArg, startArg, endArg] <- args
    , Just bs <- readBytesTerm bsArg
    , Just start <- readIntTerm startArg
    , Just end <- readIntTerm endArg
    , start >= 0
    , end >= start
    , fromIntegral end <= BS.length bs =
        pure . Just . bytesTerm $
            BS.take (fromIntegral (end - start)) (BS.drop (fromIntegral start) bs)
    | otherwise = pure Nothing

{- | replaceAt(dest, i, src): overwrite dest starting at offset i with src bytes.
Returns Nothing if i is out of bounds or src would not fit cleanly. Matches
Kore semantics: result length is len(dest) - len(src) + len(src), i.e. the
replaced slice is exactly len(src) bytes long.
-}
bytesReplaceAt :: BuiltinFunction
bytesReplaceAt args
    | length args /= 3 = arityError "BYTES.replaceAt" 3 args
    | [bsArg, iArg, srcArg] <- args
    , Just dest <- readBytesTerm bsArg
    , Just i <- readIntTerm iArg
    , Just src <- readBytesTerm srcArg =
        let delta = BS.length src
            destLen = BS.length dest
            idx = fromIntegral i
         in if delta == 0
                then pure . Just $ bytesTerm dest
                else
                    if idx < 0 || idx >= destLen || destLen == 0
                        then pure Nothing
                        else
                            pure . Just . bytesTerm $
                                BS.take idx dest <> src <> BS.drop (idx + delta) dest
    | otherwise = pure Nothing

-- | padLeftBytes(BS, N, fill): left-pad BS with fill bytes to reach length N
bytesPadLeft :: BuiltinFunction
bytesPadLeft args
    | length args /= 3 = arityError "BYTES.padLeft" 3 args
    | [bsArg, nArg, fillArg] <- args
    , Just bs <- readBytesTerm bsArg
    , Just n <- readIntTerm nArg
    , Just fill <- readFillByte fillArg =
        let len = BS.length bs
            padLen = max 0 (fromIntegral n - len)
         in pure . Just . bytesTerm $ BS.replicate padLen fill <> bs
    | otherwise = pure Nothing

-- | padRightBytes(BS, N, fill): right-pad BS with fill bytes to reach length N
bytesPadRight :: BuiltinFunction
bytesPadRight args
    | length args /= 3 = arityError "BYTES.padRight" 3 args
    | [bsArg, nArg, fillArg] <- args
    , Just bs <- readBytesTerm bsArg
    , Just n <- readIntTerm nArg
    , Just fill <- readFillByte fillArg =
        let len = BS.length bs
            padLen = max 0 (fromIntegral n - len)
         in pure . Just . bytesTerm $ bs <> BS.replicate padLen fill
    | otherwise = pure Nothing

{- | int2bytes(len, val, endianness): encode val as len bytes in the given byte order.
Positive values are zero-padded; negative values use 0xFF padding (two's complement).
-}
bytesInt2Bytes :: BuiltinFunction
bytesInt2Bytes args
    | length args /= 3 = arityError "BYTES.int2bytes" 3 args
    | [lenArg, valArg, endArg] <- args
    , Just len <- readIntTerm lenArg
    , Just val <- readIntTerm valArg
    , Just end <- readEndianness endArg =
        let pad = if val < 0 then 0xFF else 0x00
            (littleEndian, _) = BS.unfoldrN (fromIntegral len) go val
            go v
                | v == 0 = Just (pad, 0)
                | otherwise = let (d, m) = divMod v 0x100 in Just (fromIntegral m, d)
            result = case end of
                BigEndian -> BS.reverse littleEndian
                LittleEndian -> littleEndian
         in pure . Just $ bytesTerm result
    | otherwise = pure Nothing

{- | bytes2int(BS, endianness, signedness): decode BS as an integer.
BigEndian means most-significant byte first. Signed uses two's complement.
-}
bytesBytes2Int :: BuiltinFunction
bytesBytes2Int args
    | length args /= 3 = arityError "BYTES.bytes2int" 3 args
    | [bsArg, endArg, signArg] <- args
    , Just bs <- readBytesTerm bsArg
    , Just end <- readEndianness endArg
    , Just sign <- readSignedness signArg =
        let littleEndian = case end of
                LittleEndian -> bs
                BigEndian -> BS.reverse bs
            (modulus, unsigned) =
                BS.foldl'
                    (\(!place, !acc) byte -> (place * 0x100, acc + place * fromIntegral byte))
                    (1, 0)
                    littleEndian
            result = case sign of
                Unsigned -> unsigned
                Signed
                    | 2 * unsigned >= modulus -> unsigned - modulus
                    | otherwise -> unsigned
         in pure . Just $ intTerm result
    | otherwise = pure Nothing

bytesTerm :: ByteString -> Term
bytesTerm = DomainValue SortBytes

readBytesTerm :: Term -> Maybe ByteString
readBytesTerm (DomainValue SortBytes val) = Just val
readBytesTerm _other = Nothing

readFillByte :: Term -> Maybe Word8
readFillByte t = do
    i <- readIntTerm t
    if i >= 0 && i <= 255 then Just (fromIntegral i) else Nothing

data Endianness = BigEndian | LittleEndian

readEndianness :: Term -> Maybe Endianness
readEndianness (SymbolApplication sym [] [])
    | sym.name == "bigEndianBytes" = Just BigEndian
    | sym.name == "littleEndianBytes" = Just LittleEndian
readEndianness _ = Nothing

data Signedness = Signed | Unsigned

readSignedness :: Term -> Maybe Signedness
readSignedness (SymbolApplication sym [] [])
    | sym.name == "signedBytes" = Just Signed
    | sym.name == "unsignedBytes" = Just Unsigned
readSignedness _ = Nothing
