{-# LANGUAGE MagicHash #-}

module Test.Kore.Builtin.Int where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import           Data.Bits
                 ( complement, shift, xor, (.&.), (.|.) )
import qualified Data.Text as Text
import           GHC.Integer
                 ( smallInteger )
import           GHC.Integer.GMP.Internals
                 ( powModInteger, recipModInteger )
import           GHC.Integer.Logarithms
                 ( integerLog2# )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin.Int as Int
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes

import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import           Test.SMT

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genIntegerPattern :: Gen (CommonStepPattern Object)
genIntegerPattern = asPattern <$> genInteger

genConcreteIntegerPattern :: Gen (ConcreteStepPattern Object)
genConcreteIntegerPattern = asConcretePattern <$> genInteger

-- | Test a unary operator hooked to the given symbol
testUnary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer)
    -- ^ operator
    -> TestTree
testUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        let expect = asExpandedPattern $ impl a
        actual <- evaluate $ App_ symb (asPattern <$> [a])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Integer)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = asExpandedPattern $ impl a b
        actual <- evaluate $ App_ symb (asPattern <$> [a, b])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a comparison operator hooked to the given symbol
testComparison
    :: SymbolOrAlias Object
    -- ^ symbol
    -> (Integer -> Integer -> Bool)
    -- ^ implementation
    -> TestTree
testComparison symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = Test.Bool.asExpandedPattern $ impl a b
        actual <- evaluate $ App_ symb (asPattern <$> [a, b])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a partial unary operator hooked to the given symbol.
testPartialUnary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        let expect = asPartialExpandedPattern $ impl a
        actual <- evaluate $ App_ symb (asPattern <$> [a])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a partial binary operator hooked to the given symbol.
testPartialBinary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = asPartialExpandedPattern $ impl a b
        actual <- evaluate $ App_ symb (asPattern <$> [a, b])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a partial binary operator hooked to the given symbol, passing zero as
-- the second argument.
testPartialBinaryZero
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialBinaryZero symb impl =
    testPropertyWithSolver (Text.unpack name ++ " zero") $ do
        a <- forAll genInteger
        let expect = asPartialExpandedPattern $ impl a 0
        actual <- evaluate $ App_ symb (asPattern <$> [a, 0])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a partial ternary operator hooked to the given symbol.
testPartialTernary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Integer -> Integer -> Integer -> Maybe Integer)
    -- ^ operator
    -> TestTree
testPartialTernary symb impl =
    testPropertyWithSolver (Text.unpack name ++ " zero") $ do
        a <- forAll genInteger
        b <- forAll genInteger
        c <- forAll genInteger
        let expect = asPartialExpandedPattern $ impl a b c
        actual <- evaluate $ App_ symb (asPattern <$> [a, b, c])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

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
        (asPattern <$> [193, 12])
        (asExpandedPattern 1)
    , testInt
        "emod negative lhs"
        emodIntSymbol
        (asPattern <$> [-193, 12])
        (asExpandedPattern 11)
    , testInt
        "emod negative rhs"
        emodIntSymbol
        (asPattern <$> [193, -12])
        (asExpandedPattern 1)
    , testInt
        "emod both negative"
        emodIntSymbol
        (asPattern <$> [-193, -12])
        (asExpandedPattern (-1))
    , testInt
        "emod bottom"
        emodIntSymbol
        (asPattern <$> [193, 0])
        bottom
    ]

-- | Another name for asPattern.
intLiteral :: Integer -> CommonStepPattern Object
intLiteral = asPattern

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: Integer -> CommonStepPattern Object
asPattern = Int.asPattern intSort

-- | Specialize 'Int.asConcretePattern' to the builtin sort 'intSort'.
asConcretePattern :: Integer -> ConcreteStepPattern Object
asConcretePattern = Int.asConcretePattern intSort

-- | Specialize 'Int.asExpandedPattern' to the builtin sort 'intSort'.
asExpandedPattern :: Integer -> CommonExpandedPattern Object
asExpandedPattern = Int.asExpandedPattern intSort

-- | Specialize 'Int.asPartialPattern' to the builtin sort 'intSort'.
asPartialExpandedPattern :: Maybe Integer -> CommonExpandedPattern Object
asPartialExpandedPattern = Int.asPartialExpandedPattern intSort

testInt
    :: String
    -> SymbolOrAlias Object
    -> [CommonStepPattern Object]
    -> CommonExpandedPattern Object
    -> TestTree
testInt = testSymbolWithSolver evaluate
