module Test.Kore.Builtin.String where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin.String as String
import           Kore.Step.ExpandedPattern
import           Kore.Step.Pattern

import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import           Test.SMT

genString :: Gen String
genString = Gen.string (Range.linear 0 256) Gen.unicode

-- | Test a comparison operator hooked to the given symbol
testComparison
    :: TestName
    -> (String -> String -> Bool)
    -- ^ implementation
    -> SymbolOrAlias Object
    -- ^ symbol
    -> TestTree
testComparison name impl symb =
    testPropertyWithSolver name
        (do
            a <- forAll genString
            b <- forAll genString
            let expect = Test.Bool.asExpandedPattern (impl a b)
            actual <- evaluate $ App_ symb (asPattern <$> [a, b])
            (===) expect actual
        )

test_lt :: TestTree
test_lt = testComparison "STRING.lt" (<) ltStringSymbol

test_concat :: [TestTree]
test_concat =
    [ testString
        "concat simple"
        concatStringSymbol
        (asPattern <$> ["foo", "bar"])
        (asExpandedPattern "foobar")
    , testString
        "concat left identity"
        concatStringSymbol
        (asPattern <$> ["", "bar"])
        (asExpandedPattern "bar")
    , testString
        "concat right identity"
        concatStringSymbol
        (asPattern <$> ["foo", ""])
        (asExpandedPattern "foo")
    ]

test_substr :: [TestTree]
test_substr =
    [ testString
        "substr simple"
        substrStringSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern 6]
        (asExpandedPattern "foobar")
    , testString
        "substr out of bounds"
        substrStringSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern 10]
        (asExpandedPattern "foobar")
    , testString
        "substr negative start"
        substrStringSymbol
        [asPattern "foobar", Test.Int.asPattern (-10), Test.Int.asPattern 6]
        (asExpandedPattern "foobar")
    , testString
        "substr negative end"
        substrStringSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern (-1)]
        (asExpandedPattern "")
    , testString
        "substr actual substring"
        substrStringSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern 3]
        (asExpandedPattern "foo")
    ]

test_length :: [TestTree]
test_length =
    [ testString
        "length simple"
        lengthStringSymbol
        [asPattern "foobar"]
        (Test.Int.asExpandedPattern 6)
    , testString
        "length zero"
        lengthStringSymbol
        [asPattern ""]
        (Test.Int.asExpandedPattern 0)
    ]

test_find :: [TestTree]
test_find =
    [ testString
        "find simple"
        findStringSymbol
        [asPattern "foobar", asPattern "foobar", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 0)
    , testString
        "find subpattern"
        findStringSymbol
        [asPattern "foobar", asPattern "bar", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 3)
    , testString
        "find empty pattern"
        findStringSymbol
        [asPattern "foobar", asPattern "", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 0)
    , testString
        "find negative index"
        findStringSymbol
        [asPattern "foobar", asPattern "foobar", Test.Int.asPattern (-1)]
        (Test.Int.asExpandedPattern 0)
    , testString
        "find after end of string"
        findStringSymbol
        [asPattern "foobar", asPattern "bar", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern (-1))
    , testString
        "find pattern that does not exist"
        findStringSymbol
        [asPattern "foobar", asPattern "nope", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern (-1))
    ]

test_string2Base :: [TestTree]
test_string2Base =
    -- Decimal
    [ testString
        "string2Base decimal simple"
        string2BaseStringSymbol
        [asPattern "42", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern 42)
    , testString
        "string2Base decimal negative"
        string2BaseStringSymbol
        [asPattern "-42", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern (-42))
    , testString
        "string2Base decimal is bottom"
        string2BaseStringSymbol
        [asPattern "-42.3", Test.Int.asPattern 10]
        bottom
    , testString
        "string2Base decimal empty string is bottom"
        string2BaseStringSymbol
        [asPattern "", Test.Int.asPattern 10]
        bottom
    , testString
        "string2Base decimal non-number is bottom"
        string2BaseStringSymbol
        [asPattern "foobar", Test.Int.asPattern 10]
        bottom
    , testString
        "string2Base decimal from hex is bottom"
        string2BaseStringSymbol
        [asPattern "baad", Test.Int.asPattern 10]
        bottom

    -- Octal
    , testString
        "string2Base octal simple"
        string2BaseStringSymbol
        [asPattern "42", Test.Int.asPattern 8]
        (Test.Int.asExpandedPattern 34)
    , testString
        "string2Base octal negative is bottom"
        string2BaseStringSymbol
        [asPattern "-42", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal is bottom"
        string2BaseStringSymbol
        [asPattern "-42.3", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal empty string is bottom"
        string2BaseStringSymbol
        [asPattern "", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal non-number is bottom"
        string2BaseStringSymbol
        [asPattern "foobar", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal from hex is bottom"
        string2BaseStringSymbol
        [asPattern "baad", Test.Int.asPattern 8]
        bottom

    -- Hexadecimal
    , testString
        "string2Base hex simple"
        string2BaseStringSymbol
        [asPattern "42", Test.Int.asPattern 16]
        (Test.Int.asExpandedPattern 66)
    , testString
        "string2Base hex negative is bottom"
        string2BaseStringSymbol
        [asPattern "-42", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex is bottom"
        string2BaseStringSymbol
        [asPattern "-42.3", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex empty string is bottom"
        string2BaseStringSymbol
        [asPattern "", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex non-number is bottom"
        string2BaseStringSymbol
        [asPattern "foobar", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex from hex is bottom"
        string2BaseStringSymbol
        [asPattern "baad", Test.Int.asPattern 16]
        (Test.Int.asExpandedPattern 47789)
    ]

test_string2Int :: [TestTree]
test_string2Int =
    [ testString
        "string2Base decimal simple"
        string2IntStringSymbol
        [asPattern "42"]
        (Test.Int.asExpandedPattern 42)
    , testString
        "string2Int decimal negative"
        string2IntStringSymbol
        [asPattern "-42"]
        (Test.Int.asExpandedPattern (-42))
    , testString
        "string2Int decimal is bottom"
        string2IntStringSymbol
        [asPattern "-42.3"]
        bottom
    , testString
        "string2Int decimal empty string is bottom"
        string2IntStringSymbol
        [asPattern ""]
        bottom
    , testString
        "string2Int decimal non-number is bottom"
        string2IntStringSymbol
        [asPattern "foobar"]
        bottom
    , testString
        "string2Int decimal from hex is bottom"
        string2IntStringSymbol
        [asPattern "baad"]
        bottom
    ]

-- | Another name for asPattern.
stringLiteral :: String -> CommonStepPattern Object
stringLiteral = asPattern

-- | Specialize 'String.asPattern' to the builtin sort 'stringSort'.
asPattern :: String -> CommonStepPattern Object
asPattern = String.asPattern stringSort

-- | Specialize 'String.asConcretePattern' to the builtin sort 'stringSort'.
asConcretePattern :: String -> ConcreteStepPattern Object
asConcretePattern = String.asConcretePattern stringSort

-- | Specialize 'String.asExpandedPattern' to the builtin sort 'stringSort'.
asExpandedPattern :: String -> CommonExpandedPattern Object
asExpandedPattern = String.asExpandedPattern stringSort

-- | Specialize 'String.asPartialPattern' to the builtin sort 'stringSort'.
asPartialExpandedPattern :: Maybe String -> CommonExpandedPattern Object
asPartialExpandedPattern = String.asPartialExpandedPattern stringSort

testString
    :: String
    -> SymbolOrAlias Object
    -> [CommonStepPattern Object]
    -> CommonExpandedPattern Object
    -> TestTree
testString = testSymbolWithSolver evaluate
