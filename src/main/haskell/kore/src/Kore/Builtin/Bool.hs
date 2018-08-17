{- |
Module      : Kore.Builtin.Bool
Description : Built-in Boolean sort
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Bool as Bool
@
 -}
module Kore.Builtin.Bool
    ( sort
    , sortVerifiers
    , symbolVerifiers
    , patternVerifiers
    ) where

import qualified Data.HashMap.Strict as HashMap

import qualified Kore.Builtin.Builtin as Builtin

{- | Builtin name of the @Bool@ sort.
 -}
sort :: String
sort = "BOOL.Bool"

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortVerifiers :: Builtin.SortVerifiers
sortVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ("BOOL.or", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.and", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.xor", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.ne", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.eq", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.not", Builtin.verifySymbol sort [sort])
    , ("BOOL.implies", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.andThen", Builtin.verifySymbol sort [sort, sort])
    , ("BOOL.orElse", Builtin.verifySymbol sort [sort, sort])
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifiers :: Builtin.PatternVerifiers
patternVerifiers =
    -- TODO (thomas.tuegel): Not implemented
    HashMap.empty
