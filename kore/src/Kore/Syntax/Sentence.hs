{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Sentence
    ( Symbol (..)
    , groundSymbol
    , Alias (..)
    ) where

import Control.DeepSeq
       ( NFData (..) )
import Data.Hashable
       ( Hashable (..) )
import GHC.Generics
       ( Generic )

import Kore.AST.Pure as Pure
import Kore.Unparser

{- | @Symbol@ is the @head-constructor{sort-variable-list}@ part of the
@symbol-declaration@ syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).

See also: 'SymbolOrAlias'.

 -}
data Symbol = Symbol
    { symbolConstructor :: !Id
    , symbolParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable Symbol

instance NFData Symbol

instance Unparse Symbol where
    unparse Symbol { symbolConstructor, symbolParams } =
        unparse symbolConstructor
        <> parameters symbolParams

    unparse2 Symbol { symbolConstructor } =
        unparse2 symbolConstructor


-- |Given an 'Id', 'groundSymbol' produces the unparameterized 'Symbol'
-- corresponding to that argument.
groundSymbol :: Id -> Symbol
groundSymbol ctor = Symbol
    { symbolConstructor = ctor
    , symbolParams = []
    }

{-|'Alias' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-alias-declaration@ and @meta-alias-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Alias level = Alias
    { aliasConstructor :: !Id
    , aliasParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Alias level)

instance NFData (Alias level)

instance Unparse (Alias level) where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor
        <> parameters aliasParams
    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor
