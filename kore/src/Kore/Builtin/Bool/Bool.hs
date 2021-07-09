{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Builtin.Bool.Bool (
    sort,
    asBuiltin,
    asInternal,
    asPattern,

    -- * Keys
    orKey,
    andKey,
    xorKey,
    neKey,
    eqKey,
    notKey,
    impliesKey,
    andThenKey,
    orElseKey,
) where

import Data.String (
    IsString,
 )
import Data.Text (
    Text,
 )
import Kore.Internal.InternalBool
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
    fromTermLike,
 )
import Kore.Internal.TermLike (
    InternalVariable,
    Sort,
    TermLike,
    mkInternalBool,
 )
import qualified Kore.Internal.TermLike as TermLike (
    markSimplified,
 )
import Prelude.Kore

-- | Builtin name of the @Bool@ sort.
sort :: Text
sort = "BOOL.Bool"

{- | Render a 'Bool' as an internal domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Bool@ sort, but this is not
  checked.

  See also: 'sort'
-}
asInternal ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Bool ->
    TermLike variable
asInternal builtinBoolSort builtinBoolValue =
    TermLike.markSimplified . mkInternalBool $
        asBuiltin builtinBoolSort builtinBoolValue

asBuiltin ::
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Bool ->
    InternalBool
asBuiltin = InternalBool

asPattern ::
    InternalVariable variable =>
    -- | resulting sort
    Sort ->
    -- | builtin value to render
    Bool ->
    Pattern variable
asPattern resultSort = Pattern.fromTermLike . asInternal resultSort

orKey :: IsString s => s
orKey = "BOOL.or"

andKey :: IsString s => s
andKey = "BOOL.and"

xorKey :: IsString s => s
xorKey = "BOOL.xor"

neKey :: IsString s => s
neKey = "BOOL.ne"

eqKey :: IsString s => s
eqKey = "BOOL.eq"

notKey :: IsString s => s
notKey = "BOOL.not"

impliesKey :: IsString s => s
impliesKey = "BOOL.implies"

andThenKey :: IsString s => s
andThenKey = "BOOL.andThen"

orElseKey :: IsString s => s
orElseKey = "BOOL.orElse"
