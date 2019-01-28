{- |
Module      : Kore.Builtin.Bool
Description : Built-in Boolean sort
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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
    , asMetaPattern
    , asPattern
    , asExpandedPattern
    , parse
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

import           Data.Functor
                 ( ($>) )
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Text.Megaparsec as Parsec
import qualified Text.Megaparsec.Char as Parsec

import           Kore.Annotation.Valid
import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern

{- | Builtin name of the @Bool@ sort.
 -}
sort :: Text
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
    [ (orKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (andKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (xorKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (neKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (eqKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (notKey, Builtin.verifySymbol assertSort [assertSort])
    , (impliesKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (andThenKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (orElseKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifier :: Builtin.DomainValueVerifier child
patternVerifier =
    Builtin.makeEncodedDomainValueVerifier sort
        (Builtin.parseEncodeDomainValue parse Domain.BuiltinBool)

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
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Bool  -- ^ builtin value to render
    -> StepPattern Object variable
asPattern resultSort =
    mkDomainValue resultSort
        . Domain.BuiltinPattern
        . eraseAnnotations
        . asMetaPattern

asMetaPattern
    :: Functor domain
    => Bool
    -> PurePattern Meta domain variable (Valid (variable Meta) Meta)
asMetaPattern True = mkStringLiteral "true"
asMetaPattern False = mkStringLiteral "false"

asExpandedPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Bool  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asExpandedPattern resultSort =
    ExpandedPattern.fromPurePattern . asPattern resultSort

{- | @builtinFunctions@ are builtin functions on the 'Bool' sort.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
    [ (orKey, binaryOperator orKey (||))
    , (andKey, binaryOperator andKey (&&))
    , (xorKey, binaryOperator xorKey xor)
    , (neKey, binaryOperator neKey (/=))
    , (eqKey, binaryOperator eqKey (==))
    , (notKey, unaryOperator notKey not)
    , (impliesKey, binaryOperator impliesKey implies)
    , (andThenKey, binaryOperator andThenKey (&&))
    , (orElseKey, binaryOperator orElseKey (||))
    ]
  where
    unaryOperator = Builtin.unaryOperator parse asExpandedPattern
    binaryOperator = Builtin.binaryOperator parse asExpandedPattern
    xor a b = (a && not b) || (not a && b)
    implies a b = not a || b

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
