{-# LANGUAGE MagicHash #-}

module Test.Kore.Builtin.Int where

import Hedgehog hiding
    ( Concrete
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty

import Data.Bits
    ( complement
    , shift
    , xor
    , (.&.)
    , (.|.)
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

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Int as Int
import Kore.Internal.Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate

import Test.Kore
    ( elementVariableGen
    , standaloneGen
    )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genIntegerPattern :: Gen (TermLike Variable)
genIntegerPattern = asInternal <$> genInteger

genConcreteIntegerPattern :: Gen (TermLike Concrete)
genConcreteIntegerPattern = asInternal <$> genInteger

-- | Test a unary operator hooked to the given symbol
testUnary
    :: Symbol
    -- ^ hooked symbol
    -> (Integer -> Integer)
    -- ^ operator
    -> TestTree
testUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        let expect = asPattern $ impl a
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: Symbol
    -- ^ hooked symbol
    -> (Integer -> Integer -> Integer)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = asPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- | Test a comparison operator hooked to the given symbol
testComparison
    :: Symbol
    -- ^ symbol
    -> (Integer -> Integer -> Bool)
    -- ^ implementation
    -> TestTree
testComparison symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = Test.Bool.asPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- | Test a partial unary operator hooked to the given symbol.
testPartialUnary
    :: Symbol
    -- ^ hooked symbol
    -> (Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        let expect = asPartialPattern $ impl a
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- | Test a partial binary operator hooked to the given symbol.
testPartialBinary
    :: Symbol
    -- ^ hooked symbol
    -> (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = asPartialPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- | Test a partial binary operator hooked to the given symbol, passing zero as
-- the second argument.
testPartialBinaryZero
    :: Symbol
    -- ^ hooked symbol
    -> (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialBinaryZero symb impl =
    testPropertyWithSolver (Text.unpack name ++ " zero") $ do
        a <- forAll genInteger
        let expect = asPartialPattern $ impl a 0
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, 0])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- | Test a partial ternary operator hooked to the given symbol.
testPartialTernary
    :: Symbol
    -- ^ hooked symbol
    -> (Integer -> Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialTernary symb impl =
    testPropertyWithSolver (Text.unpack name ++ " zero") $ do
        a <- forAll genInteger
        b <- forAll genInteger
        c <- forAll genInteger
        let expect = asPartialPattern $ impl a b c
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b, c])
        (===) expect actual
  where
    Just name = Attribute.getHook . Attribute.hook $ symbolAttributes symb

-- Comparison operators
test_gt :: TestTree
test_gt = testComparison gtIntSymbol (>)

test_ge :: TestTree
test_ge = testComparison geIntSymbol (>=)

test_eq :: TestTree
test_eq = testComparison eqIntSymbol (==)

test_le :: TestTree
test_le = testComparison leIntSymbol (<=)

test_lt :: TestTree
test_lt = testComparison ltIntSymbol (<)

test_ne :: TestTree
test_ne = testComparison neIntSymbol (/=)

-- Ordering operations
test_min :: TestTree
test_min = testBinary minIntSymbol min

test_max :: TestTree
test_max = testBinary maxIntSymbol max

-- Arithmetic operations
test_add :: TestTree
test_add = testBinary addIntSymbol (+)

test_sub :: TestTree
test_sub = testBinary subIntSymbol (-)

test_mul :: TestTree
test_mul = testBinary mulIntSymbol (*)

test_abs :: TestTree
test_abs = testUnary absIntSymbol abs

-- Division
test_tdiv :: TestTree
test_tdiv = testPartialBinary tdivIntSymbol tdiv

tdiv :: Integer -> Integer -> Maybe Integer
tdiv n d
  | d == 0 = Nothing
  | otherwise = Just (quot n d)

test_tmod :: TestTree
test_tmod = testPartialBinary tmodIntSymbol tmod

tmod :: Integer -> Integer -> Maybe Integer
tmod n d
  | d == 0 = Nothing
  | otherwise = Just (rem n d)

test_tdivZero :: TestTree
test_tdivZero = testPartialBinaryZero tdivIntSymbol tdiv

test_tmodZero :: TestTree
test_tmodZero = testPartialBinaryZero tmodIntSymbol tmod

-- Bitwise operations
test_and :: TestTree
test_and = testBinary andIntSymbol (.&.)

test_or :: TestTree
test_or = testBinary orIntSymbol (.|.)

test_xor :: TestTree
test_xor = testBinary xorIntSymbol xor

test_not :: TestTree
test_not = testUnary notIntSymbol complement

test_shl :: TestTree
test_shl = testBinary shlIntSymbol shl
  where shl a = shift a . fromInteger

test_shr :: TestTree
test_shr = testBinary shrIntSymbol shr
  where shr a = shift a . fromInteger . negate

-- Exponential and logarithmic operations
pow :: Integer -> Integer -> Maybe Integer
pow b e
    | e < 0 = Nothing
    | otherwise = Just (b ^ e)

test_pow :: TestTree
test_pow = testPartialBinary powIntSymbol pow

powmod :: Integer -> Integer -> Integer -> Maybe Integer
powmod b e m
    | m == 0 = Nothing
    | e < 0 && recipModInteger b m == 0 = Nothing
    | otherwise = Just (powModInteger b e m)

test_powmod :: TestTree
test_powmod = testPartialTernary powmodIntSymbol powmod

log2 :: Integer -> Maybe Integer
log2 n
    | n > 0 = Just (smallInteger (integerLog2# n))
    | otherwise = Nothing

test_log2 :: TestTree
test_log2 = testPartialUnary log2IntSymbol log2

test_emod :: [TestTree]
test_emod =
    [ testInt
        "emod normal"
        emodIntSymbol
        (asInternal <$> [193, 12])
        (asPattern 1)
    , testInt
        "emod negative lhs"
        emodIntSymbol
        (asInternal <$> [-193, 12])
        (asPattern 11)
    , testInt
        "emod negative rhs"
        emodIntSymbol
        (asInternal <$> [193, -12])
        (asPattern 1)
    , testInt
        "emod both negative"
        emodIntSymbol
        (asInternal <$> [-193, -12])
        (asPattern (-1))
    , testInt
        "emod bottom"
        emodIntSymbol
        (asInternal <$> [193, 0])
        bottom
    ]

-- | Another name for asInternal.
intLiteral :: Integer -> TermLike Variable
intLiteral = asInternal

-- | Specialize 'Int.asInternal' to the builtin sort 'intSort'.
asInternal :: Ord variable => Integer -> TermLike variable
asInternal = Int.asInternal intSort

-- | Specialize 'asInternal' to the builtin sort 'intSort'.
asConcretePattern :: Integer -> TermLike Concrete
asConcretePattern = asInternal

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: Integer -> Pattern Variable
asPattern = Int.asPattern intSort

-- | Specialize 'Int.asPartialPattern' to the builtin sort 'intSort'.
asPartialPattern :: Maybe Integer -> Pattern Variable
asPartialPattern = Int.asPartialPattern intSort

testInt
    :: String
    -> Symbol
    -> [TermLike Variable]
    -> Pattern Variable
    -> TestTree
testInt name = testSymbolWithSolver evaluate name

-- | "\equal"ed internal Integers that are not equal
test_unifyEqual_NotEqual :: TestTree
test_unifyEqual_NotEqual =
    testCaseWithSMT "unifyEqual BuiltinInteger: Not Equal" $ do
        let dv1 = asInternal 1
            dv2 = asInternal 2
        actual <- evaluate $ mkEquals_ dv1 dv2
        assertEqual' "" bottom actual

-- | "\equal"ed internal Integers that are equal
test_unifyEqual_Equal :: TestTree
test_unifyEqual_Equal =
    testCaseWithSMT "unifyEqual BuiltinInteger: Equal" $ do
        let dv1 = asInternal 2
        actual <- evaluate $ mkEquals_ dv1 dv1
        assertEqual' "" top actual

-- | "\and"ed internal Integers that are not equal
test_unifyAnd_NotEqual :: TestTree
test_unifyAnd_NotEqual =
    testCaseWithSMT "unifyAnd BuiltinInteger: Not Equal" $ do
        let dv1 = asInternal 1
            dv2 = asInternal 2
        actual <- evaluate $ mkAnd dv1 dv2
        assertEqual' "" bottom actual

-- | "\and"ed internal Integers that are equal
test_unifyAnd_Equal :: TestTree
test_unifyAnd_Equal =
    testCaseWithSMT "unifyAnd BuiltinInteger: Equal" $ do
        let dv1 = asInternal 2
        actual <- evaluate $ mkAnd dv1 dv1
        assertEqual' "" (pure dv1) actual

-- | "\and"ed then "\equal"ed internal Integers that are equal
test_unifyAndEqual_Equal :: TestTree
test_unifyAndEqual_Equal =
    testCaseWithSMT "unifyAnd BuiltinInteger: Equal" $ do
        let dv = asInternal 0
        actual <- evaluate $ mkEquals_ dv $  mkAnd dv dv
        assertEqual' "" top actual

-- | Internal Integer "\and"ed with builtin function applied to variable
test_unifyAnd_Fn :: TestTree
test_unifyAnd_Fn =
    testPropertyWithSolver "unifyAnd BuiltinInteger: Equal" $ do
        var <- forAll (standaloneGen $ elementVariableGen intSort)
        let dv = asInternal 2
            fnPat = mkApplySymbol absIntSymbol  [mkElemVar var]
            expect =
                Conditional
                    { term = dv
                    , predicate = makeEqualsPredicate dv fnPat
                    , substitution = mempty
                    }
        actual <- evaluateT $ mkAnd dv fnPat
        (===) expect actual


hprop_unparse :: Property
hprop_unparse = hpropUnparse (asInternal <$> genInteger)
