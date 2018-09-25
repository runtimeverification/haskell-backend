{- |
Module      : Kore.Builtin.Int
Description : Built-in arbitrary-precision integer sort
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Int as Int
@
 -}

{-# LANGUAGE MagicHash #-}

module Kore.Builtin.Int
    ( sort
    , assertSort
    , sortDeclVerifiers
    , symbolVerifiers
    , patternVerifier
    , builtinFunctions
    , expectBuiltinDomainInt
    , asMetaPattern
    , asPattern
    , asExpandedPattern
    , asPartialExpandedPattern
    ) where

import           Control.Monad
                 ( void )
import           Control.Monad.Except
                 ( ExceptT )
import qualified Control.Monad.Except as Except
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           GHC.Integer
                 ( smallInteger )
import           GHC.Integer.GMP.Internals
                 ( powModInteger, recipModInteger )
import           GHC.Integer.Logarithms
                 ( integerLog2# )
import qualified Text.Megaparsec.Char.Lexer as Parsec

import qualified Kore.AST.Common as Kore
import           Kore.AST.MetaOrObject
                 ( Meta, Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import qualified Kore.ASTUtils.SmartPatterns as Kore
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( AttemptedFunction (..) )

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

    , ("INT.rand", Builtin.verifySymbol assertSort [assertSort])
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

{- | Abort function evaluation if the argument is not a Int domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainMap', it is a bug.

 -}
expectBuiltinDomainInt
    :: Monad m
    => String  -- ^ Context for error message
    -> CommonPurePattern Object  -- ^ Operand pattern
    -> ExceptT (AttemptedFunction Object Kore.Variable) m Integer
expectBuiltinDomainInt ctx =
    \case
        Kore.DV_ _ domain ->
            case domain of
                Kore.BuiltinDomainPattern (Kore.StringLiteral_ lit) ->
                    (return . Builtin.runParser ctx)
                        (Builtin.parseString parse lit)
                _ ->
                    Builtin.verifierBug
                        (ctx ++ ": Domain value argument is not a string")
        _ ->
            Except.throwError NotApplicable

{- | Render an 'Integer' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asPattern
    :: Kore.Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> CommonPurePattern Object
asPattern resultSort result =
    Kore.DV_ resultSort
        $ Kore.BuiltinDomainPattern
        $ asMetaPattern result

asMetaPattern :: Integer -> CommonPurePattern Meta
asMetaPattern result = Kore.StringLiteral_ $ show result

asExpandedPattern
    :: Kore.Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> CommonExpandedPattern Object
asExpandedPattern resultSort =
    ExpandedPattern.fromPurePattern . asPattern resultSort

asPartialExpandedPattern
    :: Kore.Sort Object  -- ^ resulting sort
    -> Maybe Integer  -- ^ builtin value to render
    -> CommonExpandedPattern Object
asPartialExpandedPattern resultSort =
    maybe ExpandedPattern.bottom (asExpandedPattern resultSort)

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map String Builtin.Function
builtinFunctions =
    Map.fromList
    [
      -- TODO (thomas.tuegel): Implement bit ranges.
      ("INT.bitRange", Builtin.notImplemented)
    , ("INT.signExtendBitRange", Builtin.notImplemented)

      -- TODO (thomas.tuegel): Add MonadRandom to evaluation context to
      -- implement rand and srand.
    , ("INT.rand", Builtin.notImplemented)
    , ("INT.srand", Builtin.notImplemented)

    , comparator "INT.gt" (>)
    , comparator "INT.ge" (>=)
    , comparator "INT.eq" (==)
    , comparator "INT.le" (<=)
    , comparator "INT.lt" (<)
    , comparator "INT.ne" (/=)

      -- Ordering operations
    , binaryOperator "INT.min" min
    , binaryOperator "INT.max" max

      -- Arithmetic operations
    , binaryOperator "INT.add" (+)
    , binaryOperator "INT.sub" (-)
    , binaryOperator "INT.mul" (*)
    , unaryOperator "INT.abs" abs

      -- TODO (thomas.tuegel): Implement division.
    , ("INT.ediv", Builtin.notImplemented)
    , ("INT.emod", Builtin.notImplemented)
    , partialBinaryOperator "INT.tdiv" tdiv
    , partialBinaryOperator "INT.tmod" tmod

      -- Bitwise operations
      -- TODO (thomas.tuegel): Implement bitwise operations.
    , ("INT.and", Builtin.notImplemented)
    , ("INT.or", Builtin.notImplemented)
    , ("INT.xor", Builtin.notImplemented)
    , ("INT.not", Builtin.notImplemented)
    , ("INT.shl", Builtin.notImplemented)
    , ("INT.shr", Builtin.notImplemented)

      -- Exponential and logarithmic operations
    , partialBinaryOperator "INT.pow" pow
    , partialTernaryOperator "INT.powmod" powmod
    , partialUnaryOperator "INT.log2" log2
    ]
  where
    unaryOperator name op =
        (name, Builtin.unaryOperator parse asExpandedPattern name op)
    binaryOperator name op =
        (name, Builtin.binaryOperator parse asExpandedPattern name op)
    comparator name op =
        (name, Builtin.binaryOperator parse Bool.asExpandedPattern name op)
    partialUnaryOperator name op =
        (name, Builtin.unaryOperator parse asPartialExpandedPattern name op)
    partialBinaryOperator name op =
        (name, Builtin.binaryOperator parse asPartialExpandedPattern name op)
    partialTernaryOperator name op =
        (name, Builtin.ternaryOperator parse asPartialExpandedPattern name op)
    tdiv n d
        | d == 0 = Nothing
        | otherwise = Just (quot n d)
    tmod n d
        | d == 0 = Nothing
        | otherwise = Just (rem n d)
    pow b e
        | e < 0 = Nothing
        | otherwise = Just (b ^ e)
    powmod b e m
        | m == 0 = Nothing
        | e < 0 && recipModInteger b m == 0 = Nothing
        | otherwise = Just (powModInteger b e m)
    log2 n
        | n > 0 = Just (smallInteger (integerLog2# n))
        | otherwise = Nothing
