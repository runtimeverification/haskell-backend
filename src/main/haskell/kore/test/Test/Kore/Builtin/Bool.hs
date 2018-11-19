module Test.Kore.Builtin.Bool where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import           Test.Tasty

import qualified Data.Text as Text

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import           Kore.Attribute.Hook
import qualified Kore.Builtin.Bool as Bool
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT

test_or :: TestTree
test_or = testBinary orBoolSymbol (||)

test_and :: TestTree
test_and = testBinary andBoolSymbol (&&)

test_xor :: TestTree
test_xor = testBinary xorBoolSymbol xor
  where
    xor u v = (u && not v) || (not u && v)

test_ne :: TestTree
test_ne = testBinary neBoolSymbol (/=)

test_eq :: TestTree
test_eq = testBinary eqBoolSymbol (==)

test_not :: TestTree
test_not = testUnary notBoolSymbol not

test_implies :: TestTree
test_implies = testBinary impliesBoolSymbol implies
  where
    implies u v = not u || v

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Bool -> Bool -> Bool)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = asExpandedPattern $ impl a b
        actual <- evaluate $ App_ symb (asPattern <$> [a, b])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Test a unary operator hooked to the given symbol
testUnary
    :: SymbolOrAlias Object
    -- ^ hooked symbol
    -> (Bool -> Bool)
    -- ^ operator
    -> TestTree
testUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        let expect = asExpandedPattern $ impl a
        actual <- evaluate $ App_ symb (asPattern <$> [a])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern :: Bool -> CommonStepPattern Object
asPattern = Bool.asPattern boolSort

-- | Specialize 'Bool.asExpandedPattern' to the builtin sort 'boolSort'.
asExpandedPattern :: Bool -> CommonExpandedPattern Object
asExpandedPattern = Bool.asExpandedPattern boolSort
