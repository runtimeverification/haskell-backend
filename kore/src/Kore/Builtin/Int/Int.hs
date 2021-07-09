{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Builtin.Int.Int (
    sort,
    asBuiltin,
    asInternal,
    asPattern,
    asPartialPattern,

    -- * keys
    randKey,
    srandKey,
    gtKey,
    geKey,
    eqKey,
    leKey,
    ltKey,
    neKey,
    minKey,
    maxKey,
    addKey,
    subKey,
    mulKey,
    absKey,
    edivKey,
    emodKey,
    tdivKey,
    tmodKey,
    andKey,
    orKey,
    xorKey,
    notKey,
    shlKey,
    shrKey,
    powKey,
    powmodKey,
    log2Key,
) where

import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Kore.Internal.InternalInt
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike as TermLike hiding (
    DomainValueF,
    StringLiteralF,
 )
import Prelude.Kore

-- | Builtin name of the @Int@ sort.
sort :: Text
sort = "INT.Int"

{- | Render an 'Integer' as an internal domain value pattern of the given sort.

The result sort should be hooked to the builtin @Int@ sort, but this is not
checked.

See also: 'sort'
-}
asInternal ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Integer ->
    TermLike variable
asInternal builtinIntSort builtinIntValue =
    TermLike.fromConcrete . TermLike.markSimplified . mkInternalInt $
        asBuiltin builtinIntSort builtinIntValue

asBuiltin ::
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Integer ->
    InternalInt
asBuiltin internalIntSort internalIntValue =
    InternalInt{internalIntSort, internalIntValue}

asPattern ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Integer ->
    Pattern variable
asPattern resultSort = Pattern.fromTermLike . asInternal resultSort

asPartialPattern ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Maybe Integer ->
    Pattern variable
asPartialPattern resultSort =
    maybe Pattern.bottom (asPattern resultSort)

randKey :: IsString s => s
randKey = "INT.rand"

srandKey :: IsString s => s
srandKey = "INT.srand"

gtKey :: IsString s => s
gtKey = "INT.gt"

geKey :: IsString s => s
geKey = "INT.ge"

eqKey :: IsString s => s
eqKey = "INT.eq"

leKey :: IsString s => s
leKey = "INT.le"

ltKey :: IsString s => s
ltKey = "INT.lt"

neKey :: IsString s => s
neKey = "INT.ne"

minKey :: IsString s => s
minKey = "INT.min"

maxKey :: IsString s => s
maxKey = "INT.max"

addKey :: IsString s => s
addKey = "INT.add"

subKey :: IsString s => s
subKey = "INT.sub"

mulKey :: IsString s => s
mulKey = "INT.mul"

absKey :: IsString s => s
absKey = "INT.abs"

edivKey :: IsString s => s
edivKey = "INT.ediv"

emodKey :: IsString s => s
emodKey = "INT.emod"

tdivKey :: IsString s => s
tdivKey = "INT.tdiv"

tmodKey :: IsString s => s
tmodKey = "INT.tmod"

andKey :: IsString s => s
andKey = "INT.and"

orKey :: IsString s => s
orKey = "INT.or"

xorKey :: IsString s => s
xorKey = "INT.xor"

notKey :: IsString s => s
notKey = "INT.not"

shlKey :: IsString s => s
shlKey = "INT.shl"

shrKey :: IsString s => s
shrKey = "INT.shr"

powKey :: IsString s => s
powKey = "INT.pow"

powmodKey :: IsString s => s
powmodKey = "INT.powmod"

log2Key :: IsString s => s
log2Key = "INT.log2"
