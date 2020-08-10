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
    , verifiers
    , builtinFunctions
    , expectBuiltinInt
    , extractIntDomainValue
    , asTermLike
    , asInternal
    , asPattern
    , asPartialPattern
    , parse
    , termIntEquals
      -- * keys
    , randKey
    , srandKey
    , gtKey
    , geKey
    , eqKey
    , leKey
    , ltKey
    , neKey
    , minKey
    , maxKey
    , addKey
    , subKey
    , mulKey
    , absKey
    , edivKey
    , emodKey
    , tdivKey
    , tmodKey
    , andKey
    , orKey
    , xorKey
    , notKey
    , shlKey
    , shrKey
    , powKey
    , powmodKey
    , log2Key
      -- * implementations (for testing)
    , tdiv
    , tmod
    , ediv
    , emod
    , pow
    , powmod
    , log2
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    )
import qualified Control.Monad as Monad
import Data.Bits
    ( complement
    , shift
    , xor
    , (.&.)
    , (.|.)
    )
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import GHC.Integer
    ( smallInteger
    )
import GHC.Integer.GMP.Internals
    ( powModInteger
    , recipModInteger
    )
import GHC.Integer.Logarithms
    ( integerLog2#
    )
import qualified Text.Megaparsec.Char.Lexer as Parsec

import Kore.Attribute.Hook
    ( Hook (..)
    )
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import Kore.Builtin.Int.Int
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeCeilPredicate
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Symbol
    ( symbolHook
    )
import Kore.Internal.TermLike as TermLike
import Kore.Step.Simplification.NotSimplifier
    ( NotSimplifier (..)
    )
import Kore.Step.Simplification.Simplify
    ( BuiltinAndAxiomSimplifier
    , TermSimplifier
    )
import Kore.Unification.Unify as Unify

{- | Verify that the sort is hooked to the builtin @Int@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook
        }

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
      (randKey, Builtin.verifySymbol assertSort [assertSort])
    , (srandKey, Builtin.verifySymbolArguments [assertSort])

    , (gtKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , (geKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , (eqKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , (leKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , (ltKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])
    , (neKey, Builtin.verifySymbol Bool.assertSort [assertSort, assertSort])

      -- Ordering operations
    , (minKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (maxKey, Builtin.verifySymbol assertSort [assertSort, assertSort])

      -- Arithmetic operations
    , (addKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (subKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (mulKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (absKey, Builtin.verifySymbol assertSort [assertSort])
    , (edivKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (emodKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (tdivKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (tmodKey, Builtin.verifySymbol assertSort [assertSort, assertSort])

      -- Bitwise operations
    , (andKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (orKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (xorKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (notKey, Builtin.verifySymbol assertSort [assertSort])
    , (shlKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , (shrKey, Builtin.verifySymbol assertSort [assertSort, assertSort])

      -- Exponential and logarithmic operations
    , (powKey, Builtin.verifySymbol assertSort [assertSort, assertSort])
    , ( powmodKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort, assertSort]
      )
    , (log2Key, Builtin.verifySymbol assertSort [assertSort])
    ]

{- | Verify that domain value patterns are well-formed.
 -}
patternVerifierHook :: Builtin.PatternVerifierHook
patternVerifierHook =
    Builtin.domainValuePatternVerifierHook sort patternVerifierWorker
  where
    patternVerifierWorker external =
        case externalChild of
            StringLiteral_ lit -> do
                builtinIntValue <- Builtin.parseString parse lit
                (return . BuiltinF . Domain.BuiltinInt)
                    Domain.InternalInt
                        { builtinIntSort = domainValueSort
                        , builtinIntValue
                        }
            _ -> Kore.Error.koreFail "Expected literal string"
      where
        DomainValue { domainValueSort } = external
        DomainValue { domainValueChild = externalChild } = external

-- | get the value from a (possibly encoded) domain value
extractIntDomainValue
    :: Text -- ^ error message Context
    -> Builtin child
    -> Integer
extractIntDomainValue ctx =
    \case
        Domain.BuiltinInt Domain.InternalInt { builtinIntValue } ->
            builtinIntValue
        _ ->
            Builtin.verifierBug
            $ Text.unpack ctx ++ ": Int builtin should be internal"

{- | Parse a string literal as an integer.
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
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m Integer
expectBuiltinInt ctx =
    \case
        Builtin_ domain ->
            case domain of
                Domain.BuiltinInt Domain.InternalInt { builtinIntValue } ->
                    return builtinIntValue
                _ ->
                    Builtin.verifierBug
                    $ Text.unpack ctx
                    ++ ": Domain value is not a string or internal value"
        _ -> empty

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text BuiltinAndAxiomSimplifier
builtinFunctions =
    Map.fromList
    [
      -- TODO (thomas.tuegel): Add MonadRandom to evaluation context to
      -- implement rand and srand.
      (randKey, Builtin.notImplemented)
    , (srandKey, Builtin.notImplemented)

    , comparator gtKey (>)
    , comparator geKey (>=)
    , (eqKey, Builtin.functionEvaluator evalEq)
    , comparator leKey (<=)
    , comparator ltKey (<)
    , comparator neKey (/=)

      -- Ordering operations
    , binaryOperator minKey min
    , binaryOperator maxKey max

      -- Arithmetic operations
    , binaryOperator addKey (+)
    , binaryOperator subKey (-)
    , binaryOperator mulKey (*)
    , unaryOperator absKey abs

      -- Division operations
    , partialBinaryOperator edivKey ediv
    , partialBinaryOperator emodKey emod
    , partialBinaryOperator tdivKey tdiv
    , partialBinaryOperator tmodKey tmod

      -- Bitwise operations
    , binaryOperator andKey (.&.)
    , binaryOperator orKey (.|.)
    , binaryOperator xorKey xor
    , unaryOperator notKey complement
    , binaryOperator shlKey (\a -> shift a . fromInteger)
    , binaryOperator shrKey (\a -> shift a . fromInteger . negate)

      -- Exponential and logarithmic operations
    , partialBinaryOperator powKey pow
    , partialTernaryOperator powmodKey powmod
    , partialUnaryOperator log2Key log2
    ]
  where
    unaryOperator name op =
        ( name, Builtin.unaryOperator extractIntDomainValue
            asPattern name op )
    binaryOperator name op =
        ( name, Builtin.binaryOperator extractIntDomainValue
            asPattern name op )
    comparator name op =
        ( name, Builtin.binaryOperator extractIntDomainValue
            Bool.asPattern name op )
    partialUnaryOperator name op =
        ( name, Builtin.unaryOperator extractIntDomainValue
            asPartialPattern name op )
    partialBinaryOperator name op =
        ( name, Builtin.binaryOperator extractIntDomainValue
            asPartialPattern name op )
    partialTernaryOperator name op =
        ( name, Builtin.ternaryOperator extractIntDomainValue
            asPartialPattern name op )

tdiv, tmod, ediv, emod, pow
    :: Integer -> Integer -> Maybe Integer
tdiv n d
    | d == 0 = Nothing
    | otherwise = Just (quot n d)
tmod n d
    | d == 0 = Nothing
    | otherwise = Just (rem n d)
ediv n d
    | d == 0 = Nothing
    | n < 0, d < 0, mod n d /= 0 =
        Just (1 + div (-n) (-d))
    | d < 0 = Just (quot n d)
    | otherwise = Just (div n d)
emod n d
    | d == 0 = Nothing
    | n < 0, d < 0, mod n d /= 0 =
        Just (n - d * (1 + div (-n) (-d)))
    | d < 0  = Just (rem n d)
    | otherwise = Just (mod n d)
pow b e
    | e < 0 = Nothing
    | otherwise = Just (b ^ e)

log2
    :: Integer -> Maybe Integer
log2 n
    | n > 0 = Just (smallInteger (integerLog2# n))
    | otherwise = Nothing

powmod
    :: Integer -> Integer -> Integer -> Maybe Integer
powmod b e m
    | m == 0 = Nothing
    | e < 0 && recipModInteger b m == 0 = Nothing
    | otherwise = Just (powModInteger b e m)

evalEq :: Builtin.Function
evalEq resultSort arguments@[_intLeft, _intRight] =
    concrete <|> symbolicReflexivity
  where
    concrete = do
        _intLeft <- expectBuiltinInt eqKey _intLeft
        _intRight <- expectBuiltinInt eqKey _intRight
        _intLeft == _intRight
            & Bool.asPattern resultSort
            & return

    symbolicReflexivity = do
        Monad.guard (TermLike.isFunctionPattern _intLeft)
        -- Do not need to check _intRight because we only return a result
        -- when _intLeft and _intRight are equal.
        if _intLeft == _intRight then
            True & Bool.asPattern resultSort & returnPattern
        else
            empty

    mkCeilUnlessDefined termLike
      | TermLike.isDefinedPattern termLike = Condition.topOf resultSort
      | otherwise =
        Condition.fromPredicate (makeCeilPredicate resultSort termLike)
    returnPattern = return . flip Pattern.andCondition conditions
    conditions = foldMap mkCeilUnlessDefined arguments

evalEq _ _ = Builtin.wrongArity eqKey

{- The @INT.eq hooked symbol applied to @term@-type arguments.
-}

data IntEqual term =
    IntEqual
        { symbol :: !Symbol
        , operand1, operand2 :: !term
        }
    deriving Show

{- | Match the @Int.eq@ hooked symbol.
-}
matchIntEqual :: TermLike variable -> Maybe (IntEqual (TermLike variable))
matchIntEqual (App_ symbol [operand1, operand2]) = do
    hook2 <- (getHook . symbolHook) symbol
    Monad.guard (hook2 == eqKey)
    return IntEqual { symbol, operand1, operand2 }
matchIntEqual _ = Nothing

termIntEquals
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => TermSimplifier variable unifier
    -> NotSimplifier unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
termIntEquals unifyChildren (NotSimplifier notSimplifier) a b =
    worker a b <|> worker b a
  where
    eraseTerm = Pattern.fromCondition_ . Pattern.withoutTerm
    worker termLike1 termLike2
      | Just IntEqual { operand1, operand2 } <- matchIntEqual termLike1
      , isFunctionPattern termLike1
      , Just value2 <- Bool.matchBool termLike2
      = lift $ do
        solution <-
            fmap OrPattern.fromPatterns
            <$> Unify.gather
            $ unifyChildren operand1 operand2
        let solution' = fmap eraseTerm solution
        finalSolution <-
            if value2
                then return solution'
                else notSimplifier SideCondition.top solution'
        Unify.scatter finalSolution
    worker _ _ = empty
