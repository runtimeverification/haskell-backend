module Test.Kore.Builtin.Int (
    test_gt,
    test_ge,
    test_eq,
    test_le,
    test_lt,
    test_ne,
    test_min,
    test_max,
    test_add,
    test_sub,
    test_mul,
    test_abs,
    test_tdiv,
    test_tmod,
    test_tdivZero,
    test_tmodZero,
    test_ediv_property,
    test_emod_property,
    test_edivZero,
    test_emodZero,
    test_ediv,
    test_emod,
    test_euclidian_division_theorem,
    test_and,
    test_or,
    test_xor,
    test_not,
    test_shl,
    test_shr,
    test_pow,
    test_powmod,
    test_log2,
    test_unifyEqual_NotEqual,
    test_unifyEqual_Equal,
    test_unifyAnd_NotEqual,
    test_unifyAnd_Equal,
    test_unifyAndEqual_Equal,
    test_unifyAnd_Fn,
    test_reflexivity_symbolic,
    test_symbolic_eq_not_conclusive,
    test_unifyIntEq,
    hprop_unparse,
    test_contradiction,
    --
    asInternal,
    asPattern,
    asOrPattern,
    asConcretePattern,
    asKey,
    asPartialPattern,
    genIntegerPattern,
    genConcreteIntegerPattern,
    genIntegerKey,
    genInteger,
    intLiteral,
    testInt,
) where

import Control.Monad.Trans.Maybe (
    runMaybeT,
 )
import Data.Bits (
    complement,
    shift,
    xor,
    (.&.),
    (.|.),
 )
import qualified Data.Text as Text
import Hedgehog hiding (
    Concrete,
 )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Kore.Builtin.Int (
    ediv,
    emod,
    log2,
    pow,
    powmod,
    tdiv,
    tmod,
 )
import qualified Kore.Builtin.Int as Int
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalInt
import Kore.Internal.Key as Key
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (OrPattern)
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
 )
import Kore.Simplify.AndTerms (
    termUnification,
 )
import Kore.Simplify.Data (
    runSimplifier,
    runSimplifierBranch,
    simplifyCondition,
 )
import qualified Kore.Simplify.Not as Not
import qualified Kore.Simplify.Pattern as Pattern
import Kore.Unification.UnifierT (
    evalEnvUnifierT,
 )
import Prelude.Kore
import Test.Kore (
    configElementVariableGen,
    standaloneGen,
    testId,
 )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT
import Test.Tasty
import Test.Tasty.HUnit.Ext

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genIntegerPattern :: InternalVariable variable => Gen (TermLike variable)
genIntegerPattern = asInternal <$> genInteger

genConcreteIntegerPattern :: Gen (TermLike Concrete)
genConcreteIntegerPattern = asInternal <$> genInteger

genIntegerKey :: Gen Key
genIntegerKey = asKey <$> genInteger

-- | Test a unary operator hooked to the given symbol
testUnary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Integer -> Integer) ->
    TestTree
testUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        let expect = asOrPattern $ impl a
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a])
        (===) expect actual
  where
    name = expectHook symb

-- | Test a binary operator hooked to the given symbol.
testBinary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Integer -> Integer -> Integer) ->
    TestTree
testBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = asOrPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    name = expectHook symb

-- | Test a comparison operator hooked to the given symbol
testComparison ::
    -- | symbol
    Symbol ->
    -- | implementation
    (Integer -> Integer -> Bool) ->
    TestTree
testComparison symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = Test.Bool.asOrPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    name = expectHook symb

-- | Test a partial unary operator hooked to the given symbol.
testPartialUnary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Integer -> Maybe Integer) ->
    TestTree
testPartialUnary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        let expect = asPartialOrPattern $ impl a
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a])
        (===) expect actual
  where
    name = expectHook symb

-- | Test a partial binary operator hooked to the given symbol.
testPartialBinary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Integer -> Integer -> Maybe Integer) ->
    TestTree
testPartialBinary symb impl =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        let expect = asPartialOrPattern $ impl a b
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual
  where
    name = expectHook symb

{- | Test a partial binary operator hooked to the given symbol, passing zero as
 the second argument.
-}
testPartialBinaryZero ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Integer -> Integer -> Maybe Integer) ->
    TestTree
testPartialBinaryZero symb impl =
    testPropertyWithSolver (Text.unpack name ++ " zero") $ do
        a <- forAll genInteger
        let expect = asPartialOrPattern $ impl a 0
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, 0])
        (===) expect actual
  where
    name = expectHook symb

-- | Test a partial ternary operator hooked to the given symbol.
testPartialTernary ::
    -- | hooked symbol
    Symbol ->
    -- | operator
    (Integer -> Integer -> Integer -> Maybe Integer) ->
    TestTree
testPartialTernary symb impl =
    testPropertyWithSolver (Text.unpack name ++ " zero") $ do
        a <- forAll genInteger
        b <- forAll genInteger
        c <- forAll genInteger
        let expect = asPartialOrPattern $ impl a b c
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b, c])
        (===) expect actual
  where
    name = expectHook symb

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

test_tmod :: TestTree
test_tmod = testPartialBinary tmodIntSymbol tmod

test_tdivZero :: TestTree
test_tdivZero = testPartialBinaryZero tdivIntSymbol tdiv

test_tmodZero :: TestTree
test_tmodZero = testPartialBinaryZero tmodIntSymbol tmod

test_ediv_property :: TestTree
test_ediv_property = testPartialBinary edivIntSymbol ediv

test_emod_property :: TestTree
test_emod_property = testPartialBinary emodIntSymbol emod

test_edivZero :: TestTree
test_edivZero = testPartialBinaryZero edivIntSymbol tdiv

test_emodZero :: TestTree
test_emodZero = testPartialBinaryZero emodIntSymbol tmod

test_ediv :: [TestTree]
test_ediv =
    [ testInt
        "ediv normal"
        edivIntSymbol
        (asInternal <$> [193, 12])
        (asOrPattern 16)
    , testInt
        "ediv negative lhs"
        edivIntSymbol
        (asInternal <$> [-193, 12])
        (asOrPattern (-17))
    , testInt
        "ediv negative rhs"
        edivIntSymbol
        (asInternal <$> [193, -12])
        (asOrPattern (-16))
    , testInt
        "ediv both negative"
        edivIntSymbol
        (asInternal <$> [-193, -12])
        (asOrPattern 17)
    , testInt
        "ediv bottom"
        edivIntSymbol
        (asInternal <$> [193, 0])
        OrPattern.bottom
    ]

test_emod :: [TestTree]
test_emod =
    [ testInt
        "emod normal"
        emodIntSymbol
        (asInternal <$> [193, 12])
        (asOrPattern 1)
    , testInt
        "emod negative lhs"
        emodIntSymbol
        (asInternal <$> [-193, 12])
        (asOrPattern 11)
    , testInt
        "emod negative rhs"
        emodIntSymbol
        (asInternal <$> [193, -12])
        (asOrPattern 1)
    , testInt
        "emod both negative"
        emodIntSymbol
        (asInternal <$> [-193, -12])
        (asOrPattern 11)
    , testInt
        "emod bottom"
        emodIntSymbol
        (asInternal <$> [193, 0])
        OrPattern.bottom
    ]

test_euclidian_division_theorem :: TestTree
test_euclidian_division_theorem =
    testPropertyWithSolver "Euclidian division theorem" $ do
        dividend <- forAll genInteger
        divisor <- forAll genInteger
        unless (divisor /= 0) discard
        quotient <-
            evaluate'
                edivIntSymbol
                dividend
                divisor
        remainder <-
            evaluate'
                emodIntSymbol
                dividend
                divisor
        (===) (remainder >= 0 && remainder < abs divisor) True
        (===) (divisor * quotient + remainder) dividend
  where
    evaluate' symbol a b =
        mkApplySymbol
            symbol
            (asInternal <$> [a, b])
            & evaluateT
            & fmap extractValue
    extractValue :: OrPattern RewritingVariableName -> Integer
    extractValue (OrPattern.toTermLike -> term) =
        case term of
            InternalInt_ InternalInt{internalIntValue} ->
                internalIntValue
            _ -> error "Expecting builtin int."

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
  where
    shl a = shift a . fromInteger

test_shr :: TestTree
test_shr = testBinary shrIntSymbol shr
  where
    shr a = shift a . fromInteger . negate

-- Exponential and logarithmic operations
test_pow :: TestTree
test_pow = testPartialBinary powIntSymbol pow

test_powmod :: TestTree
test_powmod = testPartialTernary powmodIntSymbol powmod

test_log2 :: TestTree
test_log2 = testPartialUnary log2IntSymbol log2

-- | Another name for asInternal.
intLiteral :: Integer -> TermLike RewritingVariableName
intLiteral = asInternal

-- | Specialize 'Int.asInternal' to the builtin sort 'intSort'.
asInternal :: InternalVariable variable => Integer -> TermLike variable
asInternal = Int.asInternal intSort

asKey :: Integer -> Key
asKey internalIntValue = from InternalInt{internalIntSort = intSort, internalIntValue}

-- | Specialize 'asInternal' to the builtin sort 'intSort'.
asConcretePattern :: Integer -> TermLike Concrete
asConcretePattern = asInternal

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: InternalVariable variable => Integer -> Pattern variable
asPattern = Int.asPattern intSort

asOrPattern :: InternalVariable variable => Integer -> OrPattern variable
asOrPattern = MultiOr.singleton . asPattern

-- | Specialize 'Int.asPartialPattern' to the builtin sort 'intSort'.
asPartialPattern ::
    InternalVariable variable => Maybe Integer -> Pattern variable
asPartialPattern = Int.asPartialPattern intSort

asPartialOrPattern ::
    InternalVariable variable => Maybe Integer -> OrPattern variable
asPartialOrPattern = MultiOr.singleton . asPartialPattern

testInt ::
    String ->
    Symbol ->
    [TermLike RewritingVariableName] ->
    OrPattern RewritingVariableName ->
    TestTree
testInt name = testSymbolWithoutSolver evaluate name

-- | "\equal"ed internal Integers that are not equal
test_unifyEqual_NotEqual :: TestTree
test_unifyEqual_NotEqual =
    testCaseWithoutSMT "unifyEqual BuiltinInteger: Not Equal" $ do
        let dv1 = asInternal 1
            dv2 = asInternal 2
        actual <- evaluate $ mkEquals_ dv1 dv2
        assertEqual' "" OrPattern.bottom actual

-- | "\equal"ed internal Integers that are equal
test_unifyEqual_Equal :: TestTree
test_unifyEqual_Equal =
    testCaseWithoutSMT "unifyEqual BuiltinInteger: Equal" $ do
        let dv1 = asInternal 2
        actual <- evaluate $ mkEquals_ dv1 dv1
        assertEqual' "" OrPattern.top actual

-- | "\and"ed internal Integers that are not equal
test_unifyAnd_NotEqual :: TestTree
test_unifyAnd_NotEqual =
    testCaseWithoutSMT "unifyAnd BuiltinInteger: Not Equal" $ do
        let dv1 = asInternal 1
            dv2 = asInternal 2
        actual <- evaluate $ mkAnd dv1 dv2
        assertEqual' "" OrPattern.bottom actual

-- | "\and"ed internal Integers that are equal
test_unifyAnd_Equal :: TestTree
test_unifyAnd_Equal =
    testCaseWithoutSMT "unifyAnd BuiltinInteger: Equal" $ do
        let dv1 = asInternal 2
        actual <- evaluate $ mkAnd dv1 dv1
        assertEqual' "" (OrPattern.fromTermLike dv1) actual

-- | "\and"ed then "\equal"ed internal Integers that are equal
test_unifyAndEqual_Equal :: TestTree
test_unifyAndEqual_Equal =
    testCaseWithoutSMT "unifyAnd BuiltinInteger: Equal" $ do
        let dv = asInternal 0
        actual <- evaluate $ mkEquals_ dv $ mkAnd dv dv
        assertEqual' "" OrPattern.top actual

-- | Internal Integer "\and"ed with builtin function applied to variable
test_unifyAnd_Fn :: TestTree
test_unifyAnd_Fn =
    testPropertyWithSolver "unifyAnd BuiltinInteger: Equal" $ do
        var <-
            forAll (standaloneGen $ configElementVariableGen intSort)
        let dv = asInternal 2
            fnPat = mkApplySymbol absIntSymbol [mkElemVar var]
            expect =
                Conditional
                    { term = dv
                    , predicate = makeEqualsPredicate dv fnPat
                    , substitution = mempty
                    }
                    & MultiOr.singleton
        actual <- evaluateT $ mkAnd dv fnPat
        (===) expect actual

test_reflexivity_symbolic :: TestTree
test_reflexivity_symbolic =
    testCaseWithoutSMT "evaluate symbolic reflexivity for equality" $ do
        let x = mkElemVar $ "x" `ofSort` intSort
            expect = Test.Bool.asOrPattern True
        actual <- evaluate $ mkApplySymbol eqIntSymbol [x, x]
        assertEqual' "" expect actual

test_symbolic_eq_not_conclusive :: TestTree
test_symbolic_eq_not_conclusive =
    testCaseWithoutSMT "evaluate symbolic equality for different variables" $ do
        let x = mkElemVar $ "x" `ofSort` intSort
            y = mkElemVar $ "y" `ofSort` intSort
            expect =
                MultiOr.singleton . fromTermLike $
                    mkApplySymbol eqIntSymbol [x, y]
        actual <- evaluate $ mkApplySymbol eqIntSymbol [x, y]
        assertEqual' "" expect actual

ofSort :: Text.Text -> Sort -> ElementVariable RewritingVariableName
idName `ofSort` sort =
    configElementVariableFromId (testId idName) sort

hprop_unparse :: Property
hprop_unparse = hpropUnparse (asInternal <$> genInteger)

test_unifyIntEq :: [TestTree]
test_unifyIntEq =
    [ testCase "\\equals(false, X ==Int Y)" $ do
        let term1 = Test.Bool.asInternal False
            term2 = eqInt (mkElemVar x) (mkElemVar y)
            expect =
                makeEqualsPredicate (mkElemVar x) (mkElemVar y)
                    & makeNotPredicate
                    & Condition.fromPredicate
                    & Pattern.fromCondition_
        -- unit test
        do
            actual <- unifyIntEq term1 term2
            let expect' = expect{term = term1}
            assertEqual "" [Just expect'] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                    & Condition.fromPredicate
                    & simplifyCondition'
            assertEqual "" [expect{term = ()}] actual
        -- integration test (see #2586)
        do
            actual <-
                makeInPredicate term1 term2
                    & Condition.fromPredicate
                    & simplifyCondition'
            assertEqual "" [expect{term = ()}] actual
        do
            actual <-
                mkAnd term1 term2
                    & Pattern.fromTermLike
                    & simplifyPattern
            assertEqual "" [expect{term = term1}] actual
    , testCase "\\equals(true, X ==Int Y)" $ do
        let term1 = Test.Bool.asInternal True
            term2 = eqInt (mkElemVar x) (mkElemVar y)
            expect =
                Condition.assign (inject x) (mkElemVar y)
                    & Pattern.fromCondition_
        -- unit test
        do
            actual <- unifyIntEq term1 term2
            -- TODO (thomas.tuegel): Remove predicate sorts to eliminate this
            -- inconsistency.
            let expect' = expect{term = term1}
            assertEqual "" [Just expect'] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                    & Condition.fromPredicate
                    & simplifyCondition'
            assertEqual "" [expect{term = ()}] actual
        -- integration test (see #2586)
        do
            actual <-
                makeInPredicate term1 term2
                    & Condition.fromPredicate
                    & simplifyCondition'
            assertEqual "" [expect{term = ()}] actual
        do
            actual <-
                mkAnd term1 term2
                    & Pattern.fromTermLike
                    & simplifyPattern
            assertEqual "" [expect{term = term1}] actual
    , testCase "\\equals(X +Int 1 ==Int Y +Int 1, false)" $ do
        let term1 =
                eqInt
                    (addInt (mkElemVar x) (asInternal 1))
                    (addInt (mkElemVar y) (asInternal 1))
            term2 = Test.Bool.asInternal False
            expect =
                makeEqualsPredicate
                    (addInt (mkElemVar x) (asInternal 1))
                    (addInt (mkElemVar y) (asInternal 1))
                    & makeNotPredicate
                    & Condition.fromPredicate
                    & Pattern.fromCondition_
        -- unit test
        do
            actual <- unifyIntEq term1 term2
            let expect' = expect{term = term2}
            assertEqual "" [Just expect'] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                    & Condition.fromPredicate
                    & simplifyCondition'
            assertEqual "" [expect{term = ()}] actual
    ]
  where
    x, y :: ElementVariable RewritingVariableName
    x = "x" `ofSort` intSort
    y = "y" `ofSort` intSort

    unifyIntEq ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        IO [Maybe (Pattern RewritingVariableName)]
    unifyIntEq term1 term2 =
        unify matched
            & runMaybeT
            & evalEnvUnifierT Not.notSimplifier
            & runSimplifierBranch testEnv
            & runNoSMT
      where
        unify Nothing = empty
        unify (Just unifyData) =
            Int.unifyIntEq
                (termUnification Not.notSimplifier)
                Not.notSimplifier
                unifyData
                & lift

        matched =
            Int.matchUnifyIntEq term1 term2
                <|> Int.matchUnifyIntEq term2 term1

    simplifyCondition' ::
        Condition RewritingVariableName ->
        IO [Condition RewritingVariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
            & runSimplifierBranch testEnv
            & runNoSMT

    simplifyPattern ::
        Pattern RewritingVariableName ->
        IO [Pattern RewritingVariableName]
    simplifyPattern pattern1 =
        Pattern.simplify pattern1
            & runSimplifier testEnv
            & runNoSMT
            & fmap OrPattern.toPatterns

test_contradiction :: TestTree
test_contradiction =
    testCase "x + y = 0 ∧ x + y = 1" $ do
        let clause0 =
                makeEqualsPredicate
                    (asInternal 0)
                    (addInt x y)
            clause1 =
                makeEqualsPredicate
                    (asInternal 1)
                    (addInt x y)
            condition =
                makeAndPredicate clause0 clause1
                    & Condition.fromPredicate
        actual <- simplifyCondition' condition
        assertEqual "expected bottom" [] actual
  where
    x, y :: TermLike RewritingVariableName
    x = mkElemVar $ ofSort "x" intSort
    y = mkElemVar $ ofSort "y" intSort

    simplifyCondition' ::
        Condition RewritingVariableName ->
        IO [Condition RewritingVariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
            & runSimplifierBranch testEnv
            & runNoSMT
