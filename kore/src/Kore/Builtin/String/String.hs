{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Builtin.String.String (
    sort,
    asBuiltin,
    asInternal,
    asPattern,
    asPartialPattern,

    -- * keys
    eqKey,
    ltKey,
    plusKey,
    string2IntKey,
    int2StringKey,
    substrKey,
    lengthKey,
    findKey,
    string2BaseKey,
    base2StringKey,
    chrKey,
    ordKey,
    token2StringKey,
    string2TokenKey,
) where

import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Kore.Internal.InternalString
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike as TermLike hiding (
    DomainValueF,
    StringLiteralF,
 )
import Prelude.Kore

-- | Builtin name of the @String@ sort.
sort :: Text
sort = "STRING.String"

{- | Render a 'Text' as an internal domain value pattern of the given sort.

The result sort should be hooked to the builtin @String@ sort, but this is not
checked.

See also: 'sort'
-}
asInternal ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Text ->
    TermLike variable
asInternal internalStringSort internalStringValue =
    TermLike.fromConcrete . mkInternalString $
        asBuiltin internalStringSort internalStringValue

asBuiltin ::
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Text ->
    InternalString
asBuiltin = InternalString

asPattern ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Text ->
    Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal resultSort

asPartialPattern ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Maybe Text ->
    Pattern variable
asPartialPattern resultSort =
    maybe Pattern.bottom (asPattern resultSort)

eqKey :: IsString s => s
eqKey = "STRING.eq"

ltKey :: IsString s => s
ltKey = "STRING.lt"

plusKey :: IsString s => s
plusKey = "STRING.concat"

string2IntKey :: IsString s => s
string2IntKey = "STRING.string2int"

int2StringKey :: IsString s => s
int2StringKey = "STRING.int2string"

substrKey :: IsString s => s
substrKey = "STRING.substr"

lengthKey :: IsString s => s
lengthKey = "STRING.length"

findKey :: IsString s => s
findKey = "STRING.find"

string2BaseKey :: IsString s => s
string2BaseKey = "STRING.string2base"

base2StringKey :: IsString s => s
base2StringKey = "STRING.base2string"

chrKey :: IsString s => s
chrKey = "STRING.chr"

ordKey :: IsString s => s
ordKey = "STRING.ord"

token2StringKey :: IsString s => s
token2StringKey = "STRING.token2string"

string2TokenKey :: IsString s => s
string2TokenKey = "STRING.string2token"
