module Test.Kore.Builtin.Bool where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import qualified Data.Text as Text

import Kore.Attribute.Hook
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Bool
import Kore.Internal.Pattern
import Kore.Internal.TermLike
import qualified SMT

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT
import Test.Tasty.HUnit.Ext

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
asInternal :: Bool -> TermLike Variable
asInternal = Bool.asInternal boolSort

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern :: Bool -> Pattern Variable
asPattern = Bool.asPattern boolSort

-- | Test a binary operator hooked to the given symbol.
testBinary
    :: Symbol
    -- ^ hooked symbol
    -> (Bool -> Bool -> Bool)
    -- ^ operator
    -> TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = asPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    Attribute.Symbol { Attribute.hook = Hook { getHook = Just name } } =
        symbolAttributes symb

-- | Test a unary operator hooked to the given symbol
testUnary
    :: Symbol
    -- ^ hooked symbol
    -> (Bool -> Bool)
    -- ^ operator
    -> TestTree
testUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        let expect = asPattern $ impl a
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a])
        (===) expect actual
  where
    Attribute.Symbol { Attribute.hook = Hook { getHook = Just name } } =
        symbolAttributes symb

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
            , mkAnd _True  _True  `becomes` pure _True
            , mkAnd _False _False `becomes` pure _False
            ]
        ]
      where
        _True  = asInternal True
        _False = asInternal False

        becomes :: HasCallStack
                => TermLike Variable
                -> Pattern Variable
                -> TestTree
        becomes makerInput expected = testCase "" $ do
            actual <-
                SMT.runSMT SMT.defaultConfig mempty
                $ SMT.withSolver
                $ evaluate makerInput
            assertEqual "" expected actual


hprop_unparse :: Property
hprop_unparse = hpropUnparse (asInternal <$> Gen.bool)
