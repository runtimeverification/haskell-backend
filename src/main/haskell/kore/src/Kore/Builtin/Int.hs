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
    , extractIntDomainValue
    , asMetaPattern
    , asPattern
    , asInternal
    , asConcretePattern
    , asExpandedPattern
    , asPartialExpandedPattern
    , parse
      -- * keys
    , bitRangeKey
    , signExtendBitRangeKey
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
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT )
import           Data.Bits
                 ( complement, shift, xor, (.&.), (.|.) )
import qualified Data.HashMap.Strict as HashMap
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Integer
                 ( smallInteger )
import           GHC.Integer.GMP.Internals
                 ( powModInteger, recipModInteger )
import           GHC.Integer.Logarithms
                 ( integerLog2# )
import qualified Text.Megaparsec.Char.Lexer as Parsec

import           Kore.Annotation.Valid
import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Variables.Fresh
import           Kore.Unparser
import           Kore.Step.Simplification.Data
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.StepperAttributes

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
      ( bitRangeKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort, assertSort]
      )
    , ( signExtendBitRangeKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort, assertSort]
      )

    , (randKey, Builtin.verifySymbol assertSort [assertSort])
    , (srandKey, Builtin.verifySymbolArguments [assertSort])

      -- TODO (thomas.tuegel): Implement builtin BOOL
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
patternVerifier :: Builtin.DomainValueVerifier child
patternVerifier =
    Builtin.makeEncodedDomainValueVerifier sort
        (Builtin.parseEncodeDomainValue parse Domain.BuiltinInteger)

-- | get the value from a (possibly encoded) domain value
extractIntDomainValue
    :: Text -- ^ error message Context
    -> DomainValue Object Domain.Builtin child
    -> Integer
extractIntDomainValue
    ctx
    dv@DomainValue {domainValueSort = _,domainValueChild }
  =
    case domainValueChild of
        Domain.BuiltinInteger int -> int
        _ -> error "Int builtin should be internal by now"
        _ -> Builtin.runParser ctx $ Builtin.parseDomainValue parse dv

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
    -> StepPattern Object variable  -- ^ Operand pattern
    -> MaybeT m Integer
expectBuiltinInt ctx =
    \case
        DV_ _ domain ->
            case domain of
                Domain.BuiltinPattern (StringLiteral_ lit) ->
                    (return . Builtin.runParser ctx)
                        (Builtin.parseString parse lit)
                Domain.BuiltinInteger int -> return int
                _ ->
                    Builtin.verifierBug
                        (Text.unpack ctx ++ ": Domain value argument is not a "
                            ++ "string or internal value")
        _ ->
            empty

{- | Render an 'Integer' as an internal domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asInternal
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> StepPattern Object variable
asInternal resultSort =
    fromConcreteStepPattern
        . mkDomainValue resultSort
        . Domain.BuiltinInteger

{- | Render an 'Integer' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> StepPattern Object variable
asPattern resultSort result =
    fromConcreteStepPattern (asConcretePattern resultSort result)

{- | Render an 'Integer' as a concrete domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'

 -}
asConcretePattern
    :: Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> ConcreteStepPattern Object
asConcretePattern domainValueSort =
    mkDomainValue domainValueSort
        . Domain.BuiltinPattern
        . eraseAnnotations
        . asMetaPattern

asMetaPattern
    :: Functor domain
    => Integer
    -> PurePattern Meta domain variable (Valid (variable Meta) Meta)
asMetaPattern result = mkStringLiteral $ Text.pack $ show result

asExpandedPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
    -> Integer  -- ^ builtin value to render
    -> ExpandedPattern Object variable
asExpandedPattern resultSort =
    ExpandedPattern.fromPurePattern . asInternal resultSort

asPartialExpandedPattern
    :: Ord (variable Object)
    => Sort Object  -- ^ resulting sort
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
      --(bitRangeKey, Builtin.notImplemented)
      (signExtendBitRangeKey, Builtin.notImplemented)

      -- TODO (thomas.tuegel): Add MonadRandom to evaluation context to
      -- implement rand and srand.
    , (randKey, Builtin.notImplemented)
    , (srandKey, Builtin.notImplemented)

    , comparator gtKey (>)
    , comparator geKey (>=)
    , comparator eqKey (==)
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

      -- TODO (thomas.tuegel): Implement division.
    , (edivKey, Builtin.notImplemented)
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
        ( name
        , Builtin.unaryOperator
          extractIntDomainValue
          asExpandedPattern
          name
          op
        )
    binaryOperator name op =
        ( name
        , Builtin.binaryOperator
          extractIntDomainValue
          asExpandedPattern
          name
          op
        )
    comparator name op =
        ( name
        , Builtin.binaryOperator
          extractIntDomainValue
          Bool.asExpandedPattern
          name
          op
        )
    partialUnaryOperator name op =
        ( name
        , Builtin.unaryOperator
          extractIntDomainValue
          asPartialExpandedPattern
          name
          op
        )
    partialBinaryOperator name op =
        ( name
        , Builtin.binaryOperator
          extractIntDomainValue
          asPartialExpandedPattern
          name
          op
        )
    partialTernaryOperator name op =
        ( name
        , Builtin.ternaryOperator
          extractIntDomainValue
          asPartialExpandedPattern
          name
          op
        )
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

bitRangeKey :: IsString s => s
bitRangeKey = "INT.bitRange"

signExtendBitRangeKey :: IsString s => s
signExtendBitRangeKey = "INT.signExtendBitRange"

randKey :: IsString s => s
randKey = "INT.rand"

srandKey :: IsString s => s
srandKey = "INT.srand"

gtKey :: IsString s => s
gtKey = "INT.gt"

geKey :: IsString s => s
geKey = "INT.ge"

eqKey :: IsString s => s
eqKey = "INT.eq"

leKey :: IsString s => s
leKey = "INT.le"

ltKey :: IsString s => s
ltKey = "INT.lt"

neKey :: IsString s => s
neKey = "INT.ne"

minKey :: IsString s => s
minKey = "INT.min"

maxKey :: IsString s => s
maxKey = "INT.max"

addKey :: IsString s => s
addKey = "INT.add"

subKey :: IsString s => s
subKey = "INT.sub"

mulKey :: IsString s => s
mulKey = "INT.mul"

absKey :: IsString s => s
absKey = "INT.abs"

edivKey :: IsString s => s
edivKey = "INT.ediv"

emodKey :: IsString s => s
emodKey = "INT.emod"

tdivKey :: IsString s => s
tdivKey = "INT.tdiv"

tmodKey :: IsString s => s
tmodKey = "INT.tmod"

andKey :: IsString s => s
andKey = "INT.and"

orKey :: IsString s => s
orKey = "INT.or"

xorKey :: IsString s => s
xorKey = "INT.xor"

notKey :: IsString s => s
notKey = "INT.not"

shlKey :: IsString s => s
shlKey = "INT.shl"

shrKey :: IsString s => s
shrKey = "INT.shr"

powKey :: IsString s => s
powKey = "INT.pow"

powmodKey :: IsString s => s
powmodKey = "INT.powmod"

log2Key :: IsString s => s
log2Key = "INT.log2"
