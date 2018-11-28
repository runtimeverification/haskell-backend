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
    , expectBuiltinInt
    , asMetaPattern
    , asPattern
    , asConcretePattern
    , asExpandedPattern
    , asPartialExpandedPattern
    , parse
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import           Control.Monad
                 ( void )
import           Data.Bits
                 ( complement, shift, xor, (.&.), (.|.) )
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Text
                 ( Text )
import           GHC.Integer
                 ( smallInteger )
import           GHC.Integer.GMP.Internals
                 ( powModInteger, recipModInteger )
import           GHC.Integer.Logarithms
                 ( integerLog2# )
import qualified Text.Megaparsec.Char.Lexer as Parsec

import           Kore.AST.Pure
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern

{- | Builtin name of the @Int@ sort.
 -}
sort :: Text
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
expectBuiltinInt
    :: Monad m
    => String  -- ^ Context for error message
    -> StepPattern Object variable  -- ^ Operand pattern
    -> MaybeT m Integer
expectBuiltinInt ctx =
    \case
        DV_ _ domain ->
            case domain of
                Domain.BuiltinPattern (StringLiteral_ lit) ->
                    (return . Builtin.runParser ctx)
                        (Builtin.parseString parse lit)
                _ ->
                    Builtin.verifierBug
                        (ctx ++ ": Domain value argument is not a string")
        _ ->
            empty

{- | Render an 'Integer' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asPattern
    :: Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> StepPattern Object variable
asPattern resultSort result =
    fromConcretePurePattern (asConcretePattern resultSort result)

{- | Render an 'Integer' as a concrete domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asConcretePattern
    :: Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> ConcreteStepPattern Object
asConcretePattern domainValueSort result =
    DV_ domainValueSort (Domain.BuiltinPattern $ asMetaPattern result)

asMetaPattern :: Functor dom => Integer -> PurePattern Meta dom var ()
asMetaPattern result = StringLiteral_ $ show result

asExpandedPattern
    :: Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asExpandedPattern resultSort =
    ExpandedPattern.fromPurePattern . asPattern resultSort

asPartialExpandedPattern
    :: Sort Object  -- ^ resulting sort
    -> Maybe Integer  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asPartialExpandedPattern resultSort =
    maybe ExpandedPattern.bottom (asExpandedPattern resultSort)

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
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
    , partialBinaryOperator "INT.emod" emod
    , partialBinaryOperator "INT.tdiv" tdiv
    , partialBinaryOperator "INT.tmod" tmod

      -- Bitwise operations
    , binaryOperator "INT.and" (.&.)
    , binaryOperator "INT.or" (.|.)
    , binaryOperator "INT.xor" xor
    , unaryOperator "INT.not" complement
    , binaryOperator "INT.shl" (\a -> shift a . fromInteger)
    , binaryOperator "INT.shr" (\a -> shift a . fromInteger . negate)

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
    emod a b
        | b == 0 = Nothing
        | b < 0  = Just (rem a b)
        | otherwise = Just (mod a b)
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
