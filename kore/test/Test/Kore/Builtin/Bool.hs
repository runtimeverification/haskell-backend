module Test.Kore.Builtin.Bool (
    test_or,
    test_orElse,
    test_and,
    test_andThen,
    test_xor,
    test_ne,
    test_eq,
    test_not,
    test_implies,
    hprop_unparse,
    test_unifyBoolValues,
    test_unifyBoolAnd,
    test_unifyBoolOr,
    test_contradiction,
    --
    asPattern,
    asOrPattern,
    asInternal,
) where

import Control.Monad.Trans.Maybe
import qualified Data.Text as Text
import Hedgehog hiding (
    test,
 )
import qualified Hedgehog.Gen as Gen
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (OrPattern)
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeEqualsPredicate,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
 )
import Kore.Simplify.Data (
    SimplifierT,
    runSimplifier,
    runSimplifierBranch,
    simplifyCondition,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Unification.UnifierT (
    UnifierT,
    runUnifierT,
 )
import Prelude.Kore
import qualified SMT
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT
import Test.Tasty
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
asInternal ::
    InternalVariable variable => Bool -> TermLike variable
asInternal = Bool.asInternal boolSort

-- | Specialize 'Bool.asPattern' to the builtin sort 'boolSort'.
asPattern :: InternalVariable variable => Bool -> Pattern variable
asPattern = Bool.asPattern boolSort

asOrPattern :: InternalVariable variable => Bool -> OrPattern variable
asOrPattern = MultiOr.singleton . asPattern

-- | Test a binary operator hooked to the given symbol.
testBinary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Bool -> Bool -> Bool) ->
    TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        b <- forAll Gen.bool
        let expect = asOrPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    name = expectHook symb

-- | Test a unary operator hooked to the given symbol
testUnary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Bool -> Bool) ->
    TestTree
testUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll Gen.bool
        let expect = asOrPattern $ impl a
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
                | value1 == value2 = [Just (Pattern.fromTermLike term1)]
                | otherwise = []
        [test "" term1 term2 result]
    ]
  where
    literals = [(_True, True), (_False, False)]

    test ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        [Maybe (Pattern RewritingVariableName)] ->
        TestTree
    test testName term1 term2 expected =
        testCase testName $ do
            case Bool.matchBools term1 term2 of
                Just unifyData -> do
                    actual <- unify term1 term2 unifyData
                    assertEqual "" expected actual
                Nothing -> assertEqual "" expected [Nothing]

    unify term1 term2 unifyData =
        run (lift $ Bool.unifyBool term1 term2 unifyData)

test_unifyBoolAnd :: [TestTree]
test_unifyBoolAnd =
    [ let term1 = _True
          term2 = andBool (mkVar x) (mkVar y)
          condition =
            Condition.assign x _True
                <> Condition.assign y _True
          result = [Just (Pattern.withCondition _True condition)]
       in test "BOOL.and - true" term1 term2 result
    , let term1 = _False
          term2 = andBool (mkVar x) (mkVar y)
          result = [Nothing]
       in test "BOOL.and - false" term1 term2 result
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        [Maybe (Pattern RewritingVariableName)] ->
        TestTree
    test testName term1 term2 expected =
        testCase testName $ do
            case Bool.matchUnifyBoolAnd term1 term2 of
                Just boolAnd -> do
                    actual <- unify term1 boolAnd
                    assertEqual "" expected actual
                Nothing -> assertEqual "" expected [Nothing]

    unify term boolAnd =
        Bool.unifyBoolAnd termSimplifier term boolAnd
            & lift
            & run

test_unifyBoolOr :: [TestTree]
test_unifyBoolOr =
    [ let term1 = _False
          term2 = orBool (mkVar x) (mkVar y)
          condition =
            Condition.assign x _False
                <> Condition.assign y _False
          result = [Just (Pattern.withCondition _False condition)]
       in test "BOOL.or - false" term1 term2 result
    , let term1 = _True
          term2 = andBool (mkVar x) (mkVar y)
          result = [Nothing]
       in test "BOOL.or - true" term1 term2 result
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        [Maybe (Pattern RewritingVariableName)] ->
        TestTree
    test testName term1 term2 expected =
        testCase testName $ do
            case Bool.matchUnifyBoolOr term1 term2 of
                Just boolOr -> do
                    actual <- unify term1 boolOr
                    assertEqual "" expected actual
                Nothing -> assertEqual "" expected [Nothing]

    unify term boolOr =
        Bool.unifyBoolOr termSimplifier term boolOr
            & lift
            & run

run :: MaybeT (UnifierT (SimplifierT SMT.NoSMT)) a -> IO [Maybe a]
run =
    runNoSMT
        . runSimplifier testEnv
        . runUnifierT Not.notSimplifier
        . runMaybeT

termSimplifier ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    UnifierT (SimplifierT SMT.NoSMT) (Pattern RewritingVariableName)
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
    simplifyCondition' ::
        Condition RewritingVariableName ->
        IO [Condition RewritingVariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
            & runSimplifierBranch testEnv
            & runNoSMT
