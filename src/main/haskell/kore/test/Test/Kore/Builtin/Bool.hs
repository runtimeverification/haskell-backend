module Test.Kore.Builtin.Bool where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.Text as Text

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Hook
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT

test_or :: TestTree
test_or = testBinary orBoolSymbol (||)

test_orElse :: TestTree
test_orElse = testBinary orElseBoolSymbol (||)

test_and :: TestTree
test_and = testBinary andBoolSymbol (&&)

test_andThen :: TestTree
test_andThen = testBinary andThenBoolSymbol (&&)

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
        actual <- evaluate $ mkApp boolSort symb (asPattern <$> [a, b])
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
        actual <- evaluate $ mkApp boolSort symb (asPattern <$> [a])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

-- | "equal"ed Bool domain values are not equal
test_unifyEqual_NotEqual :: TestTree
test_unifyEqual_NotEqual =
    testCaseWithSolver "unifyEqual BuiltinInteger: Not Equal" $ \solver -> do
        let dv1 = mkDomainValue boolSort $ Domain.BuiltinBool True
            dv2 = mkDomainValue boolSort $ Domain.BuiltinBool False
        actual <- evaluateWith solver $ mkEquals_ dv1 dv2
        assertEqual "" bottom actual

-- | "equal"ed Bool domain values are equal
test_unifyEqual_Equal :: TestTree
test_unifyEqual_Equal =
    testCaseWithSolver "unifyEqual BuiltinInteger: Equal" $ \solver -> do
        let dv1 = mkDomainValue boolSort $ Domain.BuiltinBool False
        actual <- evaluateWith solver $ mkEquals_ dv1 dv1
        assertEqual "" top actual

-- | "and"ed Bool domain values are not equal
test_unifyAnd_NotEqual :: TestTree
test_unifyAnd_NotEqual =
    testCaseWithSolver "unifyEqual BuiltinInteger: Not Equal" $ \solver -> do
        let dv1 = mkDomainValue boolSort $ Domain.BuiltinBool True
            dv2 = mkDomainValue boolSort $ Domain.BuiltinBool False
        actual <- evaluateWith solver $ mkAnd dv1 dv2
        assertEqual "" bottom actual

-- | "and"ed Bool domain values are equal
test_unifyAnd_Equal :: TestTree
test_unifyAnd_Equal =
    testCaseWithSolver "unifyEqual BuiltinInteger: Equal" $ \solver -> do
        let dv1 = mkDomainValue boolSort $ Domain.BuiltinBool False
        actual <- evaluateWith solver $ mkAnd dv1 dv1
        assertEqual "" (pure dv1) actual

{- |  \equal
        ( \dv{Bool}(True)
        , \and ( \dv{Bool}(True), \dv{Bool}(True) )
        )
    =>
      top

  internal Bools "and"ed are equal
-}
test_unifyAndEqual_Equal :: TestTree
test_unifyAndEqual_Equal =
    testCaseWithSolver "unifyAnd BuiltinInteger: Equal" $ \solver -> do
        let dv = mkDomainValue intSort $ Domain.BuiltinBool True
        actual <- evaluateWith solver $ mkEquals_ dv $  mkAnd dv dv 
        assertEqual "" top actual

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern :: Bool -> CommonStepPattern Object
asPattern = Bool.asPattern boolSort

-- | Specialize 'Bool.asExpandedPattern' to the builtin sort 'boolSort'.
asExpandedPattern :: Bool -> CommonExpandedPattern Object
asExpandedPattern = Bool.asExpandedPattern boolSort
