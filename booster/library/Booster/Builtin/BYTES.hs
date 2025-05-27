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
) where

import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Char (chr)
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
            , "substr" ~~> bytessubstrHook
            , "replaceAt" ~~> bytesreplaceAtHook
            , "padRight" ~~> bytespadRightHook
            , "padLeft" ~~> bytespadLeftHook
            , "reverse" ~~> bytesreverseHook
            , "length" ~~> byteslengthHook
            , "int2bytes" ~~> bytesint2bytesHook
            , "bytes2int" ~~> bytesbytes2intHook
            ]


bytesupdateHook
    , bytessubstrHook
    , bytesreplaceAtHook
    , bytespadRightHook
    , bytespadLeftHook
    , bytesreverseHook
    , byteslengthHook
    , bytesint2bytesHook
    , bytesbytes2intHook :: BuiltinFunction

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

-- | extract a sub-sequence [start .. end) from the bytes
bytessubstrHook [bytes, start, end]
    | BytesDV bs <- bytes
    , Just st <- readIntTerm' start
    , 0 <= st && st < BS.length bs
    , Just e <- readIntTerm' end
    , st <= e && e < BS.length bs = do
        let left = BS.take e bs -- st <= e, therefore st <= length left
        pure $ Just $ BytesDV $ BS.drop st left
bytessubstrHook other = arityError "BYTES.substr" 3 other


bytesreplaceAtHook = bytespadRightHook
bytespadRightHook = bytespadLeftHook
bytespadLeftHook = bytesreverseHook
bytesreverseHook = bytesint2bytesHook

byteslengthHook [BytesDV bs] = pure . Just . intTerm' $ BS.length bs
byteslengthHook other = arityError "BYTES.length" 1 other

bytesint2bytesHook = bytesbytes2intHook
bytesbytes2intHook = \_ -> pure Nothing

------------------------

pattern BytesDV :: ByteString -> Term
pattern BytesDV bs = DomainValue SortBytes bs
