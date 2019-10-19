{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Builtin.Bool.Bool
    ( sort
    , asBuiltin
    , asInternal
    , asTermLike
    , asPattern
      -- * Keys
    , orKey
    , andKey
    , xorKey
    , neKey
    , eqKey
    , notKey
    , impliesKey
    , andThenKey
    , orElseKey
    ) where

import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )

import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromTermLike
    )
import Kore.Internal.TermLike
    ( Concrete
    , DomainValue (DomainValue)
    , InternalVariable
    , Sort
    , TermLike
    , mkBuiltin
    , mkDomainValue
    , mkStringLiteral
    )
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse

{- | Builtin name of the @Bool@ sort.
 -}
sort :: Text
sort = "BOOL.Bool"

{- | Render a 'Bool' as an internal domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Bool@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asInternal
    :: InternalVariable variable
    => Sort  -- ^ resulting sort
    -> Bool  -- ^ builtin value to render
    -> TermLike variable
asInternal builtinBoolSort builtinBoolValue =
    TermLike.markSimplified . mkBuiltin
    $ asBuiltin builtinBoolSort builtinBoolValue

asBuiltin
    :: Sort  -- ^ resulting sort
    -> Bool  -- ^ builtin value to render
    -> Domain.Builtin (TermLike Concrete) (TermLike variable)
asBuiltin builtinBoolSort builtinBoolValue =
    Domain.BuiltinBool Domain.InternalBool
        { builtinBoolSort
        , builtinBoolValue
        }

{- | Render a 'Bool' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Bool@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asTermLike
    :: InternalVariable variable
    => Domain.InternalBool  -- ^ builtin value to render
    -> TermLike variable
asTermLike builtin =
    mkDomainValue DomainValue
        { domainValueSort = builtinBoolSort
        , domainValueChild = mkStringLiteral literal
        }
  where
    Domain.InternalBool { builtinBoolSort } = builtin
    Domain.InternalBool { builtinBoolValue = bool } = builtin
    literal
      | bool      = "true"
      | otherwise = "false"

asPattern
    :: InternalVariable variable
    => Sort  -- ^ resulting sort
    -> Bool  -- ^ builtin value to render
    -> Pattern variable
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
