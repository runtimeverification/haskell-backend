module Test.Kore.Builtin.Int
    ( test_gt, test_ge, test_eq, test_le, test_lt, test_ne
    , test_min, test_max
    , test_add, test_sub, test_mul, test_abs
    , test_tdiv, test_tmod, test_tdivZero, test_tmodZero
    , test_ediv_property, test_emod_property, test_edivZero, test_emodZero
    , test_ediv, test_emod
    , test_euclidian_division_theorem
    , test_and, test_or, test_xor, test_not
    , test_shl, test_shr
    , test_pow, test_powmod, test_log2
    , test_tdiv_evaluated_arguments
    , test_ediv_evaluated_arguments
    , test_unifyEqual_NotEqual
    , test_unifyEqual_Equal
    , test_unifyAnd_NotEqual
    , test_unifyAnd_Equal
    , test_unifyAndEqual_Equal
    , test_unifyAnd_Fn
    , test_reflexivity_symbolic
    , test_symbolic_eq_not_conclusive
    , test_unifyIntEq
    , hprop_unparse
    , test_contradiction
    --
    , asInternal
    , asPattern
    , asConcretePattern
    , asPartialPattern
    , genIntegerPattern
    , genConcreteIntegerPattern
    , genInteger
    , intLiteral
    , testInt
    ) where

import Prelude.Kore

import Hedgehog hiding
    ( Concrete
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty

import Control.Monad.Trans.Maybe
    ( runMaybeT
    )
import Data.Bits
    ( complement
    , shift
    , xor
    , (.&.)
    , (.|.)
    )
import Data.Functor
    ( (<&>)
    )
import Data.Semigroup
    ( Endo (..)
    )
import qualified Data.Text as Text

import Kore.Builtin.Int
    ( ediv
    , emod
    , log2
    , pow
    , powmod
    , tdiv
    , tmod
    )
import qualified Kore.Builtin.Int as Int
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalInt
import Kore.Internal.Pattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , mkConfigVariable
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import Kore.Step.Simplification.Data
    ( runSimplifierBranch
    , simplifyCondition
    )
import qualified Kore.Step.Simplification.Not as Not
import Kore.Unification.UnifierT
    ( evalEnvUnifierT
    )

import Test.Kore
    ( elementVariableGen
    , standaloneGen
    , testId
    )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT
import Test.Tasty.HUnit.Ext

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genIntegerPattern :: InternalVariable variable => Gen (TermLike variable)
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
    name = expectHook symb

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
    name = expectHook symb

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
    name = expectHook symb

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
    name = expectHook symb

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
    name = expectHook symb

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
    name = expectHook symb

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

test_tdiv_evaluated_arguments :: TestTree
test_tdiv_evaluated_arguments =
    testDivEvaluatedArguments tdivIntSymbol tdiv

test_tmod :: TestTree
test_tmod = testPartialBinary tmodIntSymbol tmod

test_tdivZero :: TestTree
test_tdivZero = testPartialBinaryZero tdivIntSymbol tdiv

test_tmodZero :: TestTree
test_tmodZero = testPartialBinaryZero tmodIntSymbol tmod

test_ediv_property :: TestTree
test_ediv_property = testPartialBinary edivIntSymbol ediv

test_ediv_evaluated_arguments :: TestTree
test_ediv_evaluated_arguments =
    testDivEvaluatedArguments edivIntSymbol ediv

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
        (asPattern 16)
    , testInt
        "ediv negative lhs"
        edivIntSymbol
        (asInternal <$> [-193, 12])
        (asPattern (-17))
    , testInt
        "ediv negative rhs"
        edivIntSymbol
        (asInternal <$> [193, -12])
        (asPattern (-16))
    , testInt
        "ediv both negative"
        edivIntSymbol
        (asInternal <$> [-193, -12])
        (asPattern 17)
    , testInt
        "ediv bottom"
        edivIntSymbol
        (asInternal <$> [193, 0])
        bottom
    ]

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
        (asPattern 11)
    , testInt
        "emod bottom"
        emodIntSymbol
        (asInternal <$> [193, 0])
        bottom
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
    extractValue :: Pattern RewritingVariableName -> Integer
    extractValue (Pattern.toTermLike -> term) =
        case term of
            InternalInt_ InternalInt { internalIntValue } ->
                internalIntValue
            _ -> error "Expecting builtin int."

testDivEvaluatedArguments
    :: Symbol
    -> (Integer -> Integer -> Maybe Integer)
    -> TestTree
testDivEvaluatedArguments symbol expected =
    testPropertyWithSolver (Text.unpack name) $ do
        a <- forAll genInteger
        b <- forAll genInteger
        na <- forAll $ Gen.integral (Range.linear 0 5)
        nb <- forAll $ Gen.integral (Range.linear 0 5)
        let expect = asPartialPattern $ expected a b
        actual <- evaluateT
            $ mkApplySymbol symbol [evaluated na a, evaluated nb b]
        (===) expect actual
  where
    name = expectHook edivIntSymbol <> " with evaluated arguments"
    compose n f = appEndo $ stimes (n :: Integer) (Endo f)
    evaluated n x = compose n mkEvaluated $ asInternal x

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
test_pow :: TestTree
test_pow = testPartialBinary powIntSymbol pow

test_powmod :: TestTree
test_powmod = testPartialTernary powmodIntSymbol powmod

test_log2 :: TestTree
test_log2 = testPartialUnary log2IntSymbol log2

-- | Another name for asInternal.
intLiteral :: Integer -> TermLike VariableName
intLiteral = asInternal

-- | Specialize 'Int.asInternal' to the builtin sort 'intSort'.
asInternal :: InternalVariable variable => Integer -> TermLike variable
asInternal = Int.asInternal intSort

-- | Specialize 'asInternal' to the builtin sort 'intSort'.
asConcretePattern :: Integer -> TermLike Concrete
asConcretePattern = asInternal

-- | Specialize 'Int.asPattern' to the builtin sort 'intSort'.
asPattern :: InternalVariable variable => Integer -> Pattern variable
asPattern = Int.asPattern intSort

-- | Specialize 'Int.asPartialPattern' to the builtin sort 'intSort'.
asPartialPattern
    :: InternalVariable variable => Maybe Integer -> Pattern variable
asPartialPattern = Int.asPartialPattern intSort

testInt
    :: String
    -> Symbol
    -> [TermLike RewritingVariableName]
    -> Pattern RewritingVariableName
    -> TestTree
testInt name = testSymbolWithoutSolver evaluate name

-- | "\equal"ed internal Integers that are not equal
test_unifyEqual_NotEqual :: TestTree
test_unifyEqual_NotEqual =
    testCaseWithoutSMT "unifyEqual BuiltinInteger: Not Equal" $ do
        let dv1 = asInternal 1
            dv2 = asInternal 2
        actual <- evaluate $ mkEquals_ dv1 dv2
        assertEqual' "" bottom actual

-- | "\equal"ed internal Integers that are equal
test_unifyEqual_Equal :: TestTree
test_unifyEqual_Equal =
    testCaseWithoutSMT "unifyEqual BuiltinInteger: Equal" $ do
        let dv1 = asInternal 2
        actual <- evaluate $ mkEquals_ dv1 dv1
        assertEqual' "" top actual

-- | "\and"ed internal Integers that are not equal
test_unifyAnd_NotEqual :: TestTree
test_unifyAnd_NotEqual =
    testCaseWithoutSMT "unifyAnd BuiltinInteger: Not Equal" $ do
        let dv1 = asInternal 1
            dv2 = asInternal 2
        actual <- evaluate $ mkAnd dv1 dv2
        assertEqual' "" bottom actual

-- | "\and"ed internal Integers that are equal
test_unifyAnd_Equal :: TestTree
test_unifyAnd_Equal =
    testCaseWithoutSMT "unifyAnd BuiltinInteger: Equal" $ do
        let dv1 = asInternal 2
        actual <- evaluate $ mkAnd dv1 dv1
        assertEqual' "" (Pattern.fromTermLike dv1) actual

-- | "\and"ed then "\equal"ed internal Integers that are equal
test_unifyAndEqual_Equal :: TestTree
test_unifyAndEqual_Equal =
    testCaseWithoutSMT "unifyAnd BuiltinInteger: Equal" $ do
        let dv = asInternal 0
        actual <- evaluate $ mkEquals_ dv $  mkAnd dv dv
        assertEqual' "" top actual

-- | Internal Integer "\and"ed with builtin function applied to variable
test_unifyAnd_Fn :: TestTree
test_unifyAnd_Fn =
    testPropertyWithSolver "unifyAnd BuiltinInteger: Equal" $ do
        var <-
            forAll (standaloneGen $ elementVariableGen intSort)
            <&> mapElementVariable (pure mkConfigVariable)
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

test_reflexivity_symbolic :: TestTree
test_reflexivity_symbolic =
    testCaseWithoutSMT "evaluate symbolic reflexivity for equality" $ do
        let x = mkElemVar $ "x" `ofSort` intSort
                & mapElementVariable (pure mkConfigVariable)
            expect = Test.Bool.asPattern True
        actual <- evaluate $ mkApplySymbol eqIntSymbol [x, x]
        assertEqual' "" expect actual

test_symbolic_eq_not_conclusive :: TestTree
test_symbolic_eq_not_conclusive =
    testCaseWithoutSMT "evaluate symbolic equality for different variables" $ do
        let x = mkElemVar $ "x" `ofSort` intSort
                & mapElementVariable (pure mkConfigVariable)
            y = mkElemVar $ "y" `ofSort` intSort
                & mapElementVariable (pure mkConfigVariable)
            expect = fromTermLike $ mkApplySymbol eqIntSymbol [x, y]
        actual <- evaluate $ mkApplySymbol eqIntSymbol [x, y]
        assertEqual' "" expect actual

ofSort :: Text.Text -> Sort -> ElementVariable VariableName
idName `ofSort` sort = mkElementVariable (testId idName) sort

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
            assertEqual "" [Just expect] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                & Condition.fromPredicate
                & simplifyCondition'
            assertEqual "" [expect { term = () }] actual
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
            let expect' = expect { predicate = makeTruePredicate }
            assertEqual "" [Just expect'] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                & Condition.fromPredicate
                & simplifyCondition'
            assertEqual "" [expect { term = () }] actual
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
            assertEqual "" [Just expect] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                & Condition.fromPredicate
                & simplifyCondition'
            assertEqual "" [expect { term = () }] actual
    ]
  where
    x, y :: ElementVariable VariableName
    x = "x" `ofSort` intSort
    y = "y" `ofSort` intSort

    unifyIntEq
        :: TermLike VariableName
        -> TermLike VariableName
        -> IO [Maybe (Pattern VariableName)]
    unifyIntEq term1 term2 =
        Int.unifyIntEq
            (termUnification Not.notSimplifier)
            Not.notSimplifier
            term1
            term2
        & runMaybeT
        & evalEnvUnifierT Not.notSimplifier
        & runSimplifierBranch testEnv
        & runNoSMT

    simplifyCondition'
        :: Condition VariableName
        -> IO [Condition VariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
        & runSimplifierBranch testEnv
        & runNoSMT

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
    x, y :: TermLike VariableName
    x = mkElemVar $ ofSort "x" intSort
    y = mkElemVar $ ofSort "y" intSort

    simplifyCondition'
        :: Condition VariableName
        -> IO [Condition VariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
        & runSimplifierBranch testEnv
        & runNoSMT
