module Test.Kore.Builtin.String where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import GHC.Stack
       ( HasCallStack )

import           Kore.AST.Pure
import           Kore.AST.Valid
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
            actual <- evaluate $ mkApp boolSort symb (asPattern <$> [a, b])
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
    [ Test.Int.testInt
        "length simple"
        lengthStringSymbol
        [asPattern "foobar"]
        (Test.Int.asExpandedPattern 6)
    , Test.Int.testInt
        "length zero"
        lengthStringSymbol
        [asPattern ""]
        (Test.Int.asExpandedPattern 0)
    ]

test_chr :: [TestTree]
test_chr =
    [ testString
        "STRING.chr(48) is '0'"
        chrStringSymbol
        [Test.Int.asPattern 48]
        (asExpandedPattern "0")
    , testString
        "STRING.chr(100) is 'd'"
        chrStringSymbol
        [Test.Int.asPattern 100]
        (asExpandedPattern "d")
    ]

test_ord :: [TestTree]
test_ord =
    [ Test.Int.testInt
        "STRING.ord('0') is 48"
        ordStringSymbol
        [asPattern "0"]
        (Test.Int.asExpandedPattern 48)
    , Test.Int.testInt
        "STRING.ord('d') is 100"
        ordStringSymbol
        [asPattern "d"]
        (Test.Int.asExpandedPattern 100)
    ]

test_find :: [TestTree]
test_find =
    [ Test.Int.testInt
        "find simple"
        findStringSymbol
        [asPattern "foobar", asPattern "foobar", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 0)
    , Test.Int.testInt
        "find subpattern"
        findStringSymbol
        [asPattern "foobar", asPattern "bar", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 3)
    , Test.Int.testInt
        "find empty pattern"
        findStringSymbol
        [asPattern "foobar", asPattern "", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 0)
    , Test.Int.testInt
        "find negative index"
        findStringSymbol
        [asPattern "foobar", asPattern "foobar", Test.Int.asPattern (-1)]
        (Test.Int.asExpandedPattern 0)
    , Test.Int.testInt
        "find after end of string"
        findStringSymbol
        [asPattern "foobar", asPattern "bar", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern (-1))
    , Test.Int.testInt
        "find pattern that does not exist"
        findStringSymbol
        [asPattern "foobar", asPattern "nope", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern (-1))
    ]

test_string2Base :: [TestTree]
test_string2Base =
    -- Decimal
    [ Test.Int.testInt
        "string2Base decimal simple"
        string2BaseStringSymbol
        [asPattern "42", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern 42)
    , Test.Int.testInt
        "string2Base decimal negative"
        string2BaseStringSymbol
        [asPattern "-42", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern (-42))
    , Test.Int.testInt
        "string2Base decimal is bottom"
        string2BaseStringSymbol
        [asPattern "-42.3", Test.Int.asPattern 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal empty string is bottom"
        string2BaseStringSymbol
        [asPattern "", Test.Int.asPattern 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal non-number is bottom"
        string2BaseStringSymbol
        [asPattern "foobar", Test.Int.asPattern 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal from hex is bottom"
        string2BaseStringSymbol
        [asPattern "baad", Test.Int.asPattern 10]
        bottom

    -- Octal
    , Test.Int.testInt
        "string2Base octal simple"
        string2BaseStringSymbol
        [asPattern "42", Test.Int.asPattern 8]
        (Test.Int.asExpandedPattern 34)
    , Test.Int.testInt
        "string2Base octal negative is bottom"
        string2BaseStringSymbol
        [asPattern "-42", Test.Int.asPattern 8]
        bottom
    , Test.Int.testInt
        "string2Base octal is bottom"
        string2BaseStringSymbol
        [asPattern "-42.3", Test.Int.asPattern 8]
        bottom
    , Test.Int.testInt
        "string2Base octal empty string is bottom"
        string2BaseStringSymbol
        [asPattern "", Test.Int.asPattern 8]
        bottom
    , Test.Int.testInt
        "string2Base octal non-number is bottom"
        string2BaseStringSymbol
        [asPattern "foobar", Test.Int.asPattern 8]
        bottom
    , Test.Int.testInt
        "string2Base octal from hex is bottom"
        string2BaseStringSymbol
        [asPattern "baad", Test.Int.asPattern 8]
        bottom

    -- Hexadecimal
    , Test.Int.testInt
        "string2Base hex simple"
        string2BaseStringSymbol
        [asPattern "42", Test.Int.asPattern 16]
        (Test.Int.asExpandedPattern 66)
    , Test.Int.testInt
        "string2Base hex negative is bottom"
        string2BaseStringSymbol
        [asPattern "-42", Test.Int.asPattern 16]
        bottom
    , Test.Int.testInt
        "string2Base hex is bottom"
        string2BaseStringSymbol
        [asPattern "-42.3", Test.Int.asPattern 16]
        bottom
    , Test.Int.testInt
        "string2Base hex empty string is bottom"
        string2BaseStringSymbol
        [asPattern "", Test.Int.asPattern 16]
        bottom
    , Test.Int.testInt
        "string2Base hex non-number is bottom"
        string2BaseStringSymbol
        [asPattern "foobar", Test.Int.asPattern 16]
        bottom
    , Test.Int.testInt
        "string2Base hex from hex is bottom"
        string2BaseStringSymbol
        [asPattern "baad", Test.Int.asPattern 16]
        (Test.Int.asExpandedPattern 47789)
    ]

test_string2Int :: [TestTree]
test_string2Int =
    [ Test.Int.testInt
        "string2Base decimal simple"
        string2IntStringSymbol
        [asPattern "42"]
        (Test.Int.asExpandedPattern 42)
    , Test.Int.testInt
        "string2Int decimal negative"
        string2IntStringSymbol
        [asPattern "-42"]
        (Test.Int.asExpandedPattern (-42))
    , Test.Int.testInt
        "string2Int decimal is bottom"
        string2IntStringSymbol
        [asPattern "-42.3"]
        bottom
    , Test.Int.testInt
        "string2Int decimal empty string is bottom"
        string2IntStringSymbol
        [asPattern ""]
        bottom
    , Test.Int.testInt
        "string2Int decimal non-number is bottom"
        string2IntStringSymbol
        [asPattern "foobar"]
        bottom
    , Test.Int.testInt
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
    :: HasCallStack
    => String
    -> SymbolOrAlias Object
    -> [CommonStepPattern Object]
    -> CommonExpandedPattern Object
    -> TestTree
testString name = testSymbolWithSolver evaluate name stringSort
