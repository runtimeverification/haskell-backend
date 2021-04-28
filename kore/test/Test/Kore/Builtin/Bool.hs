{-# LANGUAGE Strict #-}
module Test.Kore.Builtin.Bool
    ( test_or
    , test_orElse
    , test_and
    , test_andThen
    , test_xor
    , test_ne
    , test_eq
    , test_not
    , test_implies
    , hprop_unparse
    , test_unifyBoolValues
    , test_unifyBoolAnd
    , test_unifyBoolOr
    , test_contradiction
    --
    , asPattern
    , asInternal
    ) where

import Prelude.Kore

import Hedgehog hiding
    ( test
    )
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Control.Monad.Trans.Maybe
import qualified Data.Text as Text

import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Bool.Bool as Bool.Bool
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalBool
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeEqualsPredicate
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , configElementVariableFromId
    )
import Kore.Step.Simplification.Data
    ( SimplifierT
    , runSimplifier
    , runSimplifierBranch
    , simplifyCondition
    )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Unify
import Kore.Unification.UnifierT
    ( UnifierT
    , runUnifierT
    )
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
asInternal
    :: InternalVariable variable => Bool -> TermLike variable
asInternal = Bool.asInternal boolSort

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern
    :: InternalVariable variable => Bool -> Pattern variable
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
    name = expectHook symb

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
    name = expectHook symb

hprop_unparse :: Property
hprop_unparse = hpropUnparse (asInternal <$> Gen.bool)

test_unifyBoolValues :: [TestTree]
test_unifyBoolValues =
    [ testGroup "literals" $ do
        (term1, value1) <- literals
        (term2, value2) <- literals
        let result
              | value1 == value2 = [Just (Pattern.fromTermLike $ mkInternalBool term1)]
              | otherwise        = []
        [test "" term1 term2 result]
    ]
  where
    literals = [(internalTrue, True), (internalFalse, False)]

    test
        :: HasCallStack
        => TestName
        -> InternalBool
        -> InternalBool
        -> [Maybe (Pattern RewritingVariableName)]
        -> TestTree
    test testName bool1 bool2 expected =
        testCase testName $ do
            actual <- unify bool1 bool2
            assertEqual "" expected actual

    unify bool1 bool2 =
        run (Bool.unifyBool bool1 bool2)

test_unifyBoolAnd :: [TestTree]
test_unifyBoolAnd =
    [
        let term1 = _True
            term2 = andBool (mkVar x) (mkVar y)
            condition =
                Condition.assign x _True
                <> Condition.assign y _True
            result = [Just (Pattern.withCondition _True condition)]
        in
            test "BOOL.and - true" term1 term2 result
    ,
        let term1 = _False
            term2 = andBool (mkVar x) (mkVar y)
            result = [Nothing]
        in
            test "BOOL.and - false" term1 term2 result
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> TermLike RewritingVariableName
        -> TermLike RewritingVariableName
        -> [Maybe (Pattern RewritingVariableName)]
        -> TestTree
    test testName term1 term2 expected =
        testCase testName $ do
            case matchUnifyBoolAnd1 term1 term2 of
                Just (UnifyBoolAnd op1 op2) -> do
                    actual <- unify term1 term2 op1 op2
                    assertEqual "" expected actual
                _ -> case matchUnifyBoolAnd2 term1 term2 of
                    Just (UnifyBoolAnd op1 op2) -> do
                        actual <- unify term2 term1 op1 op2
                        assertEqual "" expected actual
                    _ -> assertEqual "" expected [Nothing]

    unify term1 term2 op1 op2 =
        run (Bool.unifyBoolAnd termSimplifier term1 term2 op1 op2)

test_unifyBoolOr :: [TestTree]
test_unifyBoolOr =
    [   let term1 = _False
            term2 = orBool (mkVar x) (mkVar y)
            condition =
                Condition.assign x _False
                <> Condition.assign y _False
            result = [Just (Pattern.withCondition _False condition)]
        in
            test "BOOL.or - false" term1 term2 result
    ,
        let term1 = _True
            term2 = andBool (mkVar x) (mkVar y)
            result = [Nothing]
        in
            test "BOOL.or - true" term1 term2 result
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> TermLike RewritingVariableName
        -> TermLike RewritingVariableName
        -> [Maybe (Pattern RewritingVariableName)]
        -> TestTree
    test testName term1 term2 expected =
        testCase testName $ do
            case matchUnifyBoolOr1 term1 term2 of
                Just (UnifyBoolOr (UnifyBoolOrArgs term op1 op2)) -> do
                    actual <- unify term op1 op2
                    assertEqual "" expected actual
                _ -> case matchUnifyBoolOr2 term1 term2 of
                    Just (UnifyBoolOr (UnifyBoolOrArgs term op1 op2)) -> do
                        actual <- unify term op1 op2
                        assertEqual "" expected actual
                    _ -> assertEqual "" expected [Nothing]

    unify term op1 op2 =
        run (Bool.unifyBoolOr termSimplifier term op1 op2)

run :: MaybeT (UnifierT (SimplifierT SMT.NoSMT)) a -> IO [Maybe a]
run =
    runNoSMT
    . runSimplifier testEnv
    . runUnifierT Not.notSimplifier
    . runMaybeT

termSimplifier
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> UnifierT (SimplifierT SMT.NoSMT) (Pattern RewritingVariableName)
termSimplifier = \term1 term2 ->
    runMaybeT (worker term1 term2 <|> worker term2 term1)
    >>= maybe (fallback term1 term2) return
  where
    worker term1 term2
      | ElemVar_ var <- term1 =
        Pattern.assign (inject var) term2
        & return
      | otherwise = empty
    fallback term1 term2 =
        mkAnd term1 term2
        & Pattern.fromTermLike
        & return

_True, _False :: TermLike RewritingVariableName
_True = asInternal True
_False = asInternal False

internalTrue, internalFalse :: InternalBool
internalTrue  = Bool.Bool.asBuiltin boolSort True
internalFalse = Bool.Bool.asBuiltin boolSort False

x, y :: SomeVariable RewritingVariableName
x = inject (configElementVariableFromId "x" boolSort)
y = inject (configElementVariableFromId "y" boolSort)

test_contradiction :: TestTree
test_contradiction =
    testCase "x andBool y = true ∧ x andBool y = false" $ do
        let clause0 =
                makeEqualsPredicate
                    _True
                    (andThenBool (mkVar x) (mkVar y))
            clause1 =
                makeEqualsPredicate
                    _False
                    (andThenBool (mkVar x) (mkVar y))
            condition =
                makeAndPredicate clause0 clause1
                & Condition.fromPredicate
        actual <- simplifyCondition' condition
        assertEqual "expected bottom" [] actual
  where
    simplifyCondition'
        :: Condition RewritingVariableName
        -> IO [Condition RewritingVariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
        & runSimplifierBranch testEnv
        & runNoSMT
