{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Builtin.String.String
    ( sort
    , asBuiltin
    , asInternal
    , asPattern
    , asTermLike
    , asPartialPattern
      -- * keys
    , ltKey
    , plusKey
    , string2IntKey
    , substrKey
    , lengthKey
    , findKey
    , string2BaseKey
    , chrKey
    , ordKey
    , token2StringKey
    , string2TokenKey
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
import Kore.Internal.TermLike as TermLike

{- | Builtin name of the @String@ sort.
 -}
sort :: Text
sort = "STRING.String"

{- | Render a 'Text' as an internal domain value pattern of the given sort.

The result sort should be hooked to the builtin @String@ sort, but this is not
checked.

See also: 'sort'

 -}
asInternal
    :: Ord variable
    => Sort  -- ^ resulting sort
    -> Text  -- ^ builtin value to render
    -> TermLike variable
asInternal internalStringSort internalStringValue =
    TermLike.fromConcrete . mkBuiltin
    $ asBuiltin internalStringSort internalStringValue

asBuiltin
    :: Sort  -- ^ resulting sort
    -> Text  -- ^ builtin value to render
    -> Domain.Builtin (TermLike Concrete) (TermLike variable)
asBuiltin internalStringSort internalStringValue =
    Domain.BuiltinString Domain.InternalString
        { internalStringSort
        , internalStringValue
        }

{- | Render an 'String' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @String@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asTermLike
    :: InternalVariable variable
    => Domain.InternalString  -- ^ builtin value to render
    -> TermLike variable
asTermLike internal =
    mkDomainValue DomainValue
        { domainValueSort = internalStringSort
        , domainValueChild = mkStringLiteral internalStringValue
        }
  where
    Domain.InternalString { internalStringSort } = internal
    Domain.InternalString { internalStringValue } = internal

asPattern
    :: InternalVariable variable
    => Sort  -- ^ resulting sort
    -> Text  -- ^ builtin value to render
    -> Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal resultSort

asPartialPattern
    :: InternalVariable variable
    => Sort  -- ^ resulting sort
    -> Maybe Text  -- ^ builtin value to render
    -> Pattern variable
asPartialPattern resultSort =
    maybe Pattern.bottom (asPattern resultSort)

ltKey :: IsString s => s
ltKey = "STRING.lt"

plusKey :: IsString s => s
plusKey = "STRING.concat"

string2IntKey :: IsString s => s
string2IntKey = "STRING.string2int"

substrKey :: IsString s => s
substrKey = "STRING.substr"

lengthKey :: IsString s => s
lengthKey = "STRING.length"

findKey :: IsString s => s
findKey = "STRING.find"

string2BaseKey :: IsString s => s
string2BaseKey = "STRING.string2base"

chrKey :: IsString s => s
chrKey = "STRING.chr"

ordKey :: IsString s => s
ordKey = "STRING.ord"

token2StringKey :: IsString s => s
token2StringKey = "STRING.token2string"

string2TokenKey :: IsString s => s
string2TokenKey = "STRING.string2token"
