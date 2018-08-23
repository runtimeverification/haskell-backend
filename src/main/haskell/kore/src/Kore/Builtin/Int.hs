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
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , patternVerifier
    ) where

import           Control.Monad
                 ( void )
import qualified Data.HashMap.Strict as HashMap
import qualified Text.Megaparsec.Char.Lexer as Parsec

import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin

{- | Builtin name of the @Int@ sort.
 -}
sort :: String
sort = "INT.Int"

{- | Verify that the sort is hooked to the builtin @Int@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort findSort = Builtin.verifySort findSort sort

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'

 -}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers = HashMap.fromList [ (sort, Builtin.verifySortDecl) ]

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [
      ( "INT.bitRange"
      , Builtin.verifySymbol assertSort [assertSort, assertSort, assertSort]
      )
    , ( "INT.signExtendBitRange"
      , Builtin.verifySymbol assertSort [assertSort, assertSort, assertSort]
      )

    , ("INT.rand", Builtin.verifySymbol assertSort [])
    , ("INT.srand", Builtin.verifySymbolArguments [assertSort])

      -- TODO (thomas.tuegel): Implement builtin BOOL
    , ("INT.gt", Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , ("INT.ge", Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , ("INT.eq", Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , ("INT.le", Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , ("INT.lt", Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , ("INT.ne", Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])

      -- Ordering operations
    , ("INT.min", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.max", Builtin.verifySymbol assertSort [assertSort, assertSort])

      -- Arithmetic operations
    , ("INT.add", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.sub", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.mul", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.abs", Builtin.verifySymbol assertSort [assertSort])
    , ("INT.ediv", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.emod", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.tdiv", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.tmod", Builtin.verifySymbol assertSort [assertSort, assertSort])

      -- Bitwise operations
    , ("INT.and", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.or", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.xor", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.not", Builtin.verifySymbol assertSort [assertSort])
    , ("INT.shl", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("INT.shr", Builtin.verifySymbol assertSort [assertSort, assertSort])

      -- Exponential and logarithmic operations
    , ("INT.pow", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ( "INT.powmod"
      , Builtin.verifySymbol assertSort [assertSort, assertSort, assertSort]
      )
    , ("INT.log2", Builtin.verifySymbol assertSort [assertSort])
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifier :: Builtin.PatternVerifier
patternVerifier =
    Builtin.verifyDomainValue sort
    (void . Builtin.parseDomainValue parse)

{- | Parse an integer string literal.
 -}
parse :: Builtin.Parser Integer
parse = Parsec.signed noSpace Parsec.decimal
  where
    noSpace = pure ()
