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
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , patternVerifier
    , builtinFunctions
    , asPattern
    ) where

import           Control.Monad
                 ( void )
import           Data.Functor
                 ( ($>) )
import           Data.HashMap.Strict
                 ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Parsec

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Builtin as Builtin

{- | Builtin name of the @Bool@ sort.
 -}
sort :: String
sort = "BOOL.Bool"

{- | Verify that the sort is hooked to the builtin @Bool@ sort.

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
    [ ("BOOL.or", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.and", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.xor", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.ne", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.eq", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.not", Builtin.verifySymbol assertSort [assertSort])
    , ("BOOL.implies", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.andThen", Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ("BOOL.orElse", Builtin.verifySymbol assertSort [assertSort, assertSort])
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifier :: Builtin.PatternVerifier
patternVerifier =
    Builtin.verifyDomainValue sort
    (void . Builtin.parseDomainValue parse)

{- | Parse an integer string literal.
 -}
parse :: Builtin.Parser Bool
parse = (Parsec.<|>) true false
  where
    true = Parsec.string "true" $> True
    false = Parsec.string "false" $> False

{- | Render a 'Bool' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Bool@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asPattern
    :: Kore.Sort Object  -- ^ resulting sort
    -> Bool  -- ^ builtin value to render
    -> CommonPurePattern Object
asPattern resultSort result =
    Kore.DV_ resultSort
        (Kore.StringLiteral_ Kore.StringLiteral
            { getStringLiteral = unparse result })
  where
    unparse :: Bool -> String
    unparse True = "true"
    unparse False = "false"

{- | @builtinFunctions@ are builtin functions on the 'Bool' sort.
 -}
builtinFunctions :: HashMap String Builtin.Function
builtinFunctions =
    HashMap.fromList
    [ ("BOOL.or", binaryOperator "BOOL.or" (||))
    , ("BOOL.and", binaryOperator "BOOL.and" (&&))
    , ("BOOL.xor", binaryOperator "BOOL.xor" xor)
    , ("BOOL.ne", binaryOperator "BOOL.ne" (/=))
    , ("BOOL.eq", binaryOperator "BOOL.eq" (==))
    , ("BOOL.not", unaryOperator "BOOL.not" not)
    , ("BOOL.implies", binaryOperator "BOOL.implies" implies)
    , ("BOOL.andThen", Builtin.notImplemented)
    , ("BOOL.orElse", Builtin.notImplemented)
    ]
  where
    unaryOperator = Builtin.unaryOperator parse asPattern
    binaryOperator = Builtin.binaryOperator parse asPattern
    xor a b = (a && not b) || (not a && b)
    implies a b = not a || b
