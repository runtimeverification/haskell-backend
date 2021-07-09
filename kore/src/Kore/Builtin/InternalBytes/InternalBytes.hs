{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Builtin.InternalBytes.InternalBytes (
    sort,
    asInternal,
    internalize,
    asPattern,

    -- * Keys
    bytes2StringKey,
    string2BytesKey,
    updateKey,
    getKey,
    substrKey,
    replaceAtKey,
    padRightKey,
    padLeftKey,
    reverseKey,
    lengthKey,
    concatKey,
    int2bytesKey,
    bytes2intKey,
    decodeBytesKey,
    encodeBytesKey,
) where

import Data.ByteString (
    ByteString,
 )
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import qualified Kore.Builtin.Encoding as Encoding
import qualified Kore.Builtin.Symbols as Builtin
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
    fromTermLike,
 )
import Kore.Internal.Symbol
import Kore.Internal.TermLike (
    InternalVariable,
    Sort,
    TermLike,
    mkInternalBytes,
 )
import qualified Kore.Internal.TermLike as TermLike (
    markSimplified,
    pattern App_,
    pattern StringLiteral_,
 )
import Prelude.Kore

-- | Builtin name for the Bytes sort.
sort :: Text
sort = "BYTES.Bytes"

{- | Render a 'ByteString' as an internal domain value of the given sort.

The result sort should be hooked to the builtin @Bytes@ sort, but this is
not checked.

See also: 'sort'.
-}
asInternal ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    ByteString ->
    TermLike variable
asInternal bytesSort bytesValue =
    TermLike.markSimplified $ mkInternalBytes bytesSort bytesValue

internalize ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
internalize =
    \case
        TermLike.App_ symbol args
            | isSymbolString2Bytes symbol
              , [TermLike.StringLiteral_ str] <- args ->
                let Symbol{symbolSorts} = symbol
                    ApplicationSorts{applicationSortsResult} = symbolSorts
                    literal = Encoding.encode8Bit str
                 in asInternal applicationSortsResult literal
        termLike -> termLike

isSymbolString2Bytes :: Symbol -> Bool
isSymbolString2Bytes = Builtin.isSymbol string2BytesKey

asPattern ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    ByteString ->
    Pattern variable
asPattern resultSort = Pattern.fromTermLike . asInternal resultSort

-- | Bytes

-- | Bytes -> String
bytes2StringKey :: IsString s => s
bytes2StringKey = "BYTES.bytes2string"

-- | String -> Bytes
string2BytesKey :: IsString s => s
string2BytesKey = "BYTES.string2bytes"

-- | Bytes -> Int -> Int -> Bytes
updateKey :: IsString s => s
updateKey = "BYTES.update"

-- | Bytes -> Int -> Int
getKey :: IsString s => s
getKey = "BYTES.get"

-- | Bytes -> Int -> Int -> Bytes
substrKey :: IsString s => s
substrKey = "BYTES.substr"

-- | Bytes -> Int -> Bytes -> Bytes
replaceAtKey :: IsString s => s
replaceAtKey = "BYTES.replaceAt"

-- | Bytes -> Int -> Int -> Bytes
padRightKey :: IsString s => s
padRightKey = "BYTES.padRight"

-- | Bytes -> Int -> Int -> Bytes
padLeftKey :: IsString s => s
padLeftKey = "BYTES.padLeft"

-- | Bytes -> Bytes
reverseKey :: IsString s => s
reverseKey = "BYTES.reverse"

-- | Bytes -> Int
lengthKey :: IsString s => s
lengthKey = "BYTES.length"

-- | Bytes -> Bytes -> Bytes
concatKey :: IsString s => s
concatKey = "BYTES.concat"

int2bytesKey :: IsString s => s
int2bytesKey = "BYTES.int2bytes"

bytes2intKey :: IsString s => s
bytes2intKey = "BYTES.bytes2int"

-- | String -> Bytes -> String
decodeBytesKey :: IsString s => s
decodeBytesKey = "BYTES.decodeBytes"

-- | String -> String -> String
encodeBytesKey :: IsString s => s
encodeBytesKey = "BYTES.encodeBytes"
