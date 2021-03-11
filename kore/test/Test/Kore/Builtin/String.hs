{-# LANGUAGE Strict #-}

module Test.Kore.Builtin.String
    ( test_eq
    , test_lt
    , test_concat
    , test_substr
    , test_length
    , test_chr
    , test_ord
    , test_find
    , test_string2Base
    , test_string2Int
    , test_int2String
    , test_token2String
    , test_string2Token
    , test_unifyStringEq
    , test_contradiction
    --
    , asPattern
    , asInternal
    ) where

import Prelude.Kore

import Hedgehog hiding
    ( Concrete
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty

import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import Control.Monad.Trans.Maybe
    ( runMaybeT
    )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.String as String
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , configElementVariableFromId
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
    ( testId
    )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import Test.SMT
import Test.Tasty.HUnit.Ext

genString :: Gen Text
genString = Gen.text (Range.linear 0 256) Gen.unicode

-- | Test a comparison operator hooked to the given symbol
testComparison
    :: TestName
    -> (Text -> Text -> Bool)
    -- ^ implementation
    -> Symbol
    -- ^ symbol
    -> TestTree
testComparison name impl symb =
    testPropertyWithSolver name $ do
        a <- forAll genString
        b <- forAll genString
        let expect = Test.Bool.asPattern (impl a b)
        actual <- evaluateT $ mkApplySymbol symb (asInternal <$> [a, b])
        (===) expect actual

test_eq :: TestTree
test_eq = testComparison "STRING.eq" (==) eqStringSymbol

test_lt :: TestTree
test_lt = testComparison "STRING.lt" (<) ltStringSymbol

test_concat :: [TestTree]
test_concat =
    [ testString
        "concat simple"
        concatStringSymbol
        (asInternal <$> ["foo", "bar"])
        (asPattern "foobar")
    , testString
        "concat left identity"
        concatStringSymbol
        (asInternal <$> ["", "bar"])
        (asPattern "bar")
    , testString
        "concat right identity"
        concatStringSymbol
        (asInternal <$> ["foo", ""])
        (asPattern "foo")
    ]

test_substr :: [TestTree]
test_substr =
    [ testString
        "substr simple"
        substrStringSymbol
        [asInternal "foobar", Test.Int.asInternal 0, Test.Int.asInternal 6]
        (asPattern "foobar")
    , testString
        "substr out of bounds"
        substrStringSymbol
        [asInternal "foobar", Test.Int.asInternal 0, Test.Int.asInternal 10]
        (asPattern "foobar")
    , testString
        "substr negative start"
        substrStringSymbol
        [asInternal "foobar", Test.Int.asInternal (-10), Test.Int.asInternal 6]
        (asPattern "foobar")
    , testString
        "substr negative end"
        substrStringSymbol
        [asInternal "foobar", Test.Int.asInternal 0, Test.Int.asInternal (-1)]
        (asPattern "")
    , testString
        "substr actual substring"
        substrStringSymbol
        [asInternal "foobar", Test.Int.asInternal 0, Test.Int.asInternal 3]
        (asPattern "foo")
    ]

test_length :: [TestTree]
test_length =
    [ Test.Int.testInt
        "length simple"
        lengthStringSymbol
        [asInternal "foobar"]
        (Test.Int.asPattern 6)
    , Test.Int.testInt
        "length zero"
        lengthStringSymbol
        [asInternal ""]
        (Test.Int.asPattern 0)
    ]

test_chr :: [TestTree]
test_chr =
    [ testString
        "STRING.chr(48) is '0'"
        chrStringSymbol
        [Test.Int.asInternal 48]
        (asPattern "0")
    , testString
        "STRING.chr(100) is 'd'"
        chrStringSymbol
        [Test.Int.asInternal 100]
        (asPattern "d")
    ]

test_ord :: [TestTree]
test_ord =
    [ Test.Int.testInt
        "STRING.ord('0') is 48"
        ordStringSymbol
        [asInternal "0"]
        (Test.Int.asPattern 48)
    , Test.Int.testInt
        "STRING.ord('d') is 100"
        ordStringSymbol
        [asInternal "d"]
        (Test.Int.asPattern 100)
    , Test.Int.testInt
        "STRING.ord('') is bottom"
        ordStringSymbol
        [asInternal ""]
        bottom
    , Test.Int.testInt
        "STRING.ord('foo') is bottom"
        ordStringSymbol
        [asInternal "foo"]
        bottom
    ]

test_find :: [TestTree]
test_find =
    [ Test.Int.testInt
        "find simple"
        findStringSymbol
        [asInternal "foobar", asInternal "foobar", Test.Int.asInternal 0]
        (Test.Int.asPattern 0)
    , Test.Int.testInt
        "find subpattern"
        findStringSymbol
        [asInternal "foobar", asInternal "bar", Test.Int.asInternal 0]
        (Test.Int.asPattern 3)
    , Test.Int.testInt
        "find empty pattern"
        findStringSymbol
        [asInternal "foobar", asInternal "", Test.Int.asInternal 0]
        (Test.Int.asPattern 0)
    , Test.Int.testInt
        "find negative index"
        findStringSymbol
        [asInternal "foobar", asInternal "foobar", Test.Int.asInternal (-1)]
        (Test.Int.asPattern 0)
    , Test.Int.testInt
        "find after end of string"
        findStringSymbol
        [asInternal "foobar", asInternal "bar", Test.Int.asInternal 10]
        (Test.Int.asPattern (-1))
    , Test.Int.testInt
        "find pattern that does not exist"
        findStringSymbol
        [asInternal "foobar", asInternal "nope", Test.Int.asInternal 0]
        (Test.Int.asPattern (-1))
    ]

test_string2Base :: [TestTree]
test_string2Base =
    -- Decimal
    [ Test.Int.testInt
        "string2Base decimal simple"
        string2BaseStringSymbol
        [asInternal "42", Test.Int.asInternal 10]
        (Test.Int.asPattern 42)
    , Test.Int.testInt
        "string2Base decimal negative"
        string2BaseStringSymbol
        [asInternal "-42", Test.Int.asInternal 10]
        (Test.Int.asPattern (-42))
    , Test.Int.testInt
        "string2Base decimal is bottom"
        string2BaseStringSymbol
        [asInternal "-42.3", Test.Int.asInternal 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal empty string is bottom"
        string2BaseStringSymbol
        [asInternal "", Test.Int.asInternal 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal non-number is bottom"
        string2BaseStringSymbol
        [asInternal "foobar", Test.Int.asInternal 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal from hex is bottom"
        string2BaseStringSymbol
        [asInternal "baad", Test.Int.asInternal 10]
        bottom

    -- Octal
    , Test.Int.testInt
        "string2Base octal simple"
        string2BaseStringSymbol
        [asInternal "42", Test.Int.asInternal 8]
        (Test.Int.asPattern 34)
    , Test.Int.testInt
        "string2Base octal negative is bottom"
        string2BaseStringSymbol
        [asInternal "-42", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal is bottom"
        string2BaseStringSymbol
        [asInternal "-42.3", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal empty string is bottom"
        string2BaseStringSymbol
        [asInternal "", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal non-number is bottom"
        string2BaseStringSymbol
        [asInternal "foobar", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal from hex is bottom"
        string2BaseStringSymbol
        [asInternal "baad", Test.Int.asInternal 8]
        bottom

    -- Hexadecimal
    , Test.Int.testInt
        "string2Base hex simple"
        string2BaseStringSymbol
        [asInternal "42", Test.Int.asInternal 16]
        (Test.Int.asPattern 66)
    , Test.Int.testInt
        "string2Base hex negative"
        string2BaseStringSymbol
        [asInternal "-42", Test.Int.asInternal 16]
        (Test.Int.asPattern (-66))
    , Test.Int.testInt
        "string2Base hex is bottom"
        string2BaseStringSymbol
        [asInternal "-42.3", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex empty string is bottom"
        string2BaseStringSymbol
        [asInternal "", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex non-number is bottom"
        string2BaseStringSymbol
        [asInternal "foobar", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex from hex"
        string2BaseStringSymbol
        [asInternal "baad", Test.Int.asInternal 16]
        (Test.Int.asPattern 47789)
    ]

test_string2Int :: [TestTree]
test_string2Int =
    [ Test.Int.testInt
        "string2Base decimal simple"
        string2IntStringSymbol
        [asInternal "42"]
        (Test.Int.asPattern 42)
    , Test.Int.testInt
        "string2Int decimal negative"
        string2IntStringSymbol
        [asInternal "-42"]
        (Test.Int.asPattern (-42))
    , Test.Int.testInt
        "string2Int decimal is bottom"
        string2IntStringSymbol
        [asInternal "-42.3"]
        bottom
    , Test.Int.testInt
        "string2Int decimal empty string is bottom"
        string2IntStringSymbol
        [asInternal ""]
        bottom
    , Test.Int.testInt
        "string2Int decimal non-number is bottom"
        string2IntStringSymbol
        [asInternal "foobar"]
        bottom
    , Test.Int.testInt
        "string2Int decimal from hex is bottom"
        string2IntStringSymbol
        [asInternal "baad"]
        bottom
    ]

test_int2String :: [TestTree]
test_int2String =
    [ testString
        "int2String basic example"
        int2StringStringSymbol
        [Test.Int.asInternal 42]
        (asPattern "42")
    , testString
        "int2String decimal negative"
        int2StringStringSymbol
        [Test.Int.asInternal (-42)]
        (asPattern "-42")
    ]

test_token2String :: [TestTree]
test_token2String =
    [ testString
        "STRING.token2string(\\dv{userTokenSortId{}}('test')) is 'test'"
        token2StringStringSymbol
        [Builtin.makeDomainValueTerm userTokenSort "test"]
        (asPattern "test")
    ]

test_string2Token :: [TestTree]
test_string2Token =
    [ testString
        "STRING.string2token('test') is \\dv{userTokenSortId{}}('test')"
        string2TokenStringSymbol
        [asInternal "test"]
        (Builtin.makeDomainValuePattern userTokenSort "test")
    ]

-- | Specialize 'String.asInternal' to the builtin sort 'stringSort'.
asInternal :: InternalVariable variable => Text -> TermLike variable
asInternal = String.asInternal stringSort

-- | Specialize 'String.asPattern' to the builtin sort 'stringSort'.
asPattern :: Text -> Pattern RewritingVariableName
asPattern = String.asPattern stringSort

testString
    :: HasCallStack
    => String
    -> Symbol
    -> [TermLike RewritingVariableName]
    -> Pattern RewritingVariableName
    -> TestTree
testString name = testSymbolWithoutSolver evaluate name

ofSort :: Text.Text -> Sort -> ElementVariable RewritingVariableName
idName `ofSort` sort = configElementVariableFromId (testId idName) sort

test_unifyStringEq :: [TestTree]
test_unifyStringEq =
    [ testCase "\\equals(false, X ==String Y)" $ do
        let term1 = Test.Bool.asInternal False
            term2 = eqString (mkElemVar x) (mkElemVar y)
            expect =
                makeEqualsPredicate (mkElemVar x) (mkElemVar y)
                & makeNotPredicate
                & Condition.fromPredicate
                & Pattern.fromCondition_
        -- unit test
        do
            actual <- unifyStringEq term1 term2
            assertEqual "" [Just expect] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                & Condition.fromPredicate
                & simplifyCondition'
            assertEqual "" [expect { term = () }] actual
    , testCase "\\equals(true, X ==String Y)" $ do
        let term1 = Test.Bool.asInternal True
            term2 = eqString (mkElemVar x) (mkElemVar y)
            expect =
                Condition.assign (inject x) (mkElemVar y)
                & Pattern.fromCondition_
        -- unit test
        do
            actual <- unifyStringEq term1 term2
            let expect' = expect { predicate = makeTruePredicate }
            assertEqual "" [Just expect'] actual
        -- integration test
        do
            actual <-
                makeEqualsPredicate term1 term2
                & Condition.fromPredicate
                & simplifyCondition'
            assertEqual "" [expect { term = () }] actual
    ]
  where
    unifyStringEq
        :: TermLike RewritingVariableName
        -> TermLike RewritingVariableName
        -> IO [Maybe (Pattern RewritingVariableName)]
    unifyStringEq term1 term2 =
        String.unifyStringEq
            (termUnification Not.notSimplifier)
            Not.notSimplifier
            term1
            term2
        & runMaybeT
        & evalEnvUnifierT Not.notSimplifier
        & runSimplifierBranch testEnv
        & runNoSMT

    simplifyCondition'
        :: Condition RewritingVariableName
        -> IO [Condition RewritingVariableName]
    simplifyCondition' condition =
        simplifyCondition SideCondition.top condition
        & runSimplifierBranch testEnv
        & runNoSMT

x, y :: ElementVariable RewritingVariableName
x = "x" `ofSort` stringSort
y = "y" `ofSort` stringSort

test_contradiction :: TestTree
test_contradiction =
    testCase "concatString(x, y) = \"zero\" ∧ concatString(x, y) = \"one\"" $ do
        let clause0 =
                makeEqualsPredicate
                    (asInternal "zero")
                    (concatString (mkElemVar x) (mkElemVar y))
            clause1 =
                makeEqualsPredicate
                    (asInternal "one")
                    (concatString (mkElemVar x) (mkElemVar y))
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
