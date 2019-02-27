module Test.Kore.Builtin.Bool where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Terse

import qualified Data.Text as Text

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Hook
import qualified Kore.Builtin.Bool as Bool
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Comparators ()
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

-- | Specialize 'Bool.asInternal' to the builtin sort 'boolSort'.
asInternal :: Bool -> CommonStepPattern Object
asInternal = Bool.asInternal boolSort

-- | Specialize 'Bool.asExpandedPattern' to the builtin sort 'boolSort'.
asExpandedPattern :: Bool -> CommonExpandedPattern Object
asExpandedPattern = Bool.asExpandedPattern boolSort

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
        actual <- evaluate $ mkApp boolSort symb (asInternal <$> [a, b])
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
        actual <- evaluate $ mkApp boolSort symb (asInternal <$> [a])
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools symb

test_simplification :: TestTree
test_simplification =
    testGroup "simplification of operators with constant arguments"
        [ testGroup "equality"
            [ mkEquals_ _True  _False `becomes` bottom
            , mkEquals_ _False _True  `becomes` bottom
            , mkEquals_ _True  _True  `becomes` top
            , mkEquals_ _False _False `becomes` top
            ]
        , testGroup "and"
            [ mkAnd _True  _False `becomes` bottom
            , mkAnd _False _True  `becomes` bottom
            , mkAnd _True  _True  `becomes` (pure _True)
            , mkAnd _False _False `becomes` (pure _False)
            ]
        ]
      where
        _True  = asInternal True
        _False = asInternal False

        becomes :: HasCallStack
                => CommonStepPattern Object
                -> CommonExpandedPattern Object
                -> TestTree
        becomes makerInput =
            wrapped_maker_expected withSolver
                (\solver -> evaluateWith solver makerInput)

hprop_unparse :: Property
hprop_unparse = hpropUnparse (asInternal <$> Gen.bool)
