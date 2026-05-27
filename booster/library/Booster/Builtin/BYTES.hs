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
import Booster.Builtin.INT (readIntTerm)
import Booster.Pattern.Base

builtinsBYTES :: Map ByteString BuiltinFunction
builtinsBYTES =
    Map.mapKeys ("BYTES." <>) $
        Map.fromList
            [ "empty" ~~> bytesEmpty
            , "padLeft" ~~> bytesPadLeft
            , "padRight" ~~> bytesPadRight
            , "concat" ~~> bytesConcat
            , "length" ~~> bytesLength
            ]

-- | .Bytes constant: empty byte string
bytesEmpty :: BuiltinFunction
bytesEmpty args
    | null args = pure . Just $ bytesTerm ""
    | otherwise = arityError "BYTES.empty" 0 args

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

bytesTerm :: ByteString -> Term
bytesTerm = DomainValue SortBytes

readBytesTerm :: Term -> Maybe ByteString
readBytesTerm (DomainValue SortBytes val) = Just val
readBytesTerm _other = Nothing

readFillByte :: Term -> Maybe Word8
readFillByte t = do
    i <- readIntTerm t
    if i >= 0 && i <= 255 then Just (fromIntegral i) else Nothing
