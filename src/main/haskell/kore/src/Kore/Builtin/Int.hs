{- |
Module      : Kore.Builtin.Int
Description : Built-in arbitrary-precision integer sort
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Int as Int
@
 -}
module Kore.Builtin.Int
    ( sort
    , sortVerifiers
    , symbolVerifiers
    , patternVerifiers
    ) where

import qualified Data.HashMap.Strict as HashMap

import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin

{- | Builtin name of the @Int@ sort.
 -}
sort :: String
sort = "INT.Int"

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
    [
      ("INT.bitRange", Builtin.verifySymbol sort [sort, sort, sort])
    , ("INT.signExtendBitRange", Builtin.verifySymbol sort [sort, sort, sort])

    , ("INT.rand", Builtin.verifySymbol sort [])
    , ("INT.srand", Builtin.verifySymbolArguments [sort])

      -- TODO (thomas.tuegel): Implement builtin BOOL
    , ("INT.gt", Builtin.verifySymbol Bool.sort [sort, sort])
    , ("INT.ge", Builtin.verifySymbol Bool.sort [sort, sort])
    , ("INT.eq", Builtin.verifySymbol Bool.sort [sort, sort])
    , ("INT.le", Builtin.verifySymbol Bool.sort [sort, sort])
    , ("INT.lt", Builtin.verifySymbol Bool.sort [sort, sort])
    , ("INT.ne", Builtin.verifySymbol Bool.sort [sort, sort])

      -- Ordering operations
    , ("INT.min", Builtin.verifySymbol sort [sort, sort])
    , ("INT.max", Builtin.verifySymbol sort [sort, sort])

      -- Arithmetic operations
    , ("INT.add", Builtin.verifySymbol sort [sort, sort])
    , ("INT.sub", Builtin.verifySymbol sort [sort, sort])
    , ("INT.mul", Builtin.verifySymbol sort [sort, sort])
    , ("INT.abs", Builtin.verifySymbol sort [sort])
    , ("INT.ediv", Builtin.verifySymbol sort [sort, sort])
    , ("INT.emod", Builtin.verifySymbol sort [sort, sort])
    , ("INT.tdiv", Builtin.verifySymbol sort [sort, sort])
    , ("INT.tmod", Builtin.verifySymbol sort [sort, sort])

      -- Bitwise operations
    , ("INT.and", Builtin.verifySymbol sort [sort, sort])
    , ("INT.or", Builtin.verifySymbol sort [sort, sort])
    , ("INT.xor", Builtin.verifySymbol sort [sort, sort])
    , ("INT.not", Builtin.verifySymbol sort [sort])
    , ("INT.shl", Builtin.verifySymbol sort [sort, sort])
    , ("INT.shr", Builtin.verifySymbol sort [sort, sort])

      -- Exponential and logarithmic operations
    , ("INT.pow", Builtin.verifySymbol sort [sort, sort])
    , ("INT.powmod", Builtin.verifySymbol sort [sort, sort, sort])
    , ("INT.log2", Builtin.verifySymbol sort [sort])
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifiers :: Builtin.PatternVerifiers
patternVerifiers =
    -- TODO (thomas.tuegel): Not implemented
    HashMap.empty
