module Test.Kore.Builtin.String where

import           Hedgehog hiding
                 ( Concrete )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import Data.Text
       ( Text )
import GHC.Stack
       ( HasCallStack )

import qualified Kore.Builtin.String as String
import           Kore.Internal.TermLike
import           Kore.Step.Pattern

import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import           Test.SMT

genString :: Gen Text
genString = Gen.text (Range.linear 0 256) Gen.unicode

-- | Test a comparison operator hooked to the given symbol
testComparison
    :: TestName
    -> (Text -> Text -> Bool)
    -- ^ implementation
    -> SymbolOrAlias
    -- ^ symbol
    -> TestTree
testComparison name impl symb =
    testPropertyWithSolver name
        (do
            a <- forAll genString
            b <- forAll genString
            let expect = Test.Bool.asPattern (impl a b)
            actual <- evaluate $ mkApp boolSort symb (asTermLike <$> [a, b])
            (===) expect actual
        )

test_lt :: TestTree
test_lt = testComparison "STRING.lt" (<) ltStringSymbol

test_concat :: [TestTree]
test_concat =
    [ testString
        "concat simple"
        concatStringSymbol
        (asTermLike <$> ["foo", "bar"])
        (asPattern "foobar")
    , testString
        "concat left identity"
        concatStringSymbol
        (asTermLike <$> ["", "bar"])
        (asPattern "bar")
    , testString
        "concat right identity"
        concatStringSymbol
        (asTermLike <$> ["foo", ""])
        (asPattern "foo")
    ]

test_substr :: [TestTree]
test_substr =
    [ testString
        "substr simple"
        substrStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 0, Test.Int.asInternal 6]
        (asPattern "foobar")
    , testString
        "substr out of bounds"
        substrStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 0, Test.Int.asInternal 10]
        (asPattern "foobar")
    , testString
        "substr negative start"
        substrStringSymbol
        [asTermLike "foobar", Test.Int.asInternal (-10), Test.Int.asInternal 6]
        (asPattern "foobar")
    , testString
        "substr negative end"
        substrStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 0, Test.Int.asInternal (-1)]
        (asPattern "")
    , testString
        "substr actual substring"
        substrStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 0, Test.Int.asInternal 3]
        (asPattern "foo")
    ]

test_length :: [TestTree]
test_length =
    [ Test.Int.testInt
        "length simple"
        lengthStringSymbol
        [asTermLike "foobar"]
        (Test.Int.asPattern 6)
    , Test.Int.testInt
        "length zero"
        lengthStringSymbol
        [asTermLike ""]
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
        [asTermLike "0"]
        (Test.Int.asPattern 48)
    , Test.Int.testInt
        "STRING.ord('d') is 100"
        ordStringSymbol
        [asTermLike "d"]
        (Test.Int.asPattern 100)
    , Test.Int.testInt
        "STRING.ord('') is bottom"
        ordStringSymbol
        [asTermLike ""]
        bottom
    , Test.Int.testInt
        "STRING.ord('foo') is bottom"
        ordStringSymbol
        [asTermLike "foo"]
        bottom
    ]

test_find :: [TestTree]
test_find =
    [ Test.Int.testInt
        "find simple"
        findStringSymbol
        [asTermLike "foobar", asTermLike "foobar", Test.Int.asInternal 0]
        (Test.Int.asPattern 0)
    , Test.Int.testInt
        "find subpattern"
        findStringSymbol
        [asTermLike "foobar", asTermLike "bar", Test.Int.asInternal 0]
        (Test.Int.asPattern 3)
    , Test.Int.testInt
        "find empty pattern"
        findStringSymbol
        [asTermLike "foobar", asTermLike "", Test.Int.asInternal 0]
        (Test.Int.asPattern 0)
    , Test.Int.testInt
        "find negative index"
        findStringSymbol
        [asTermLike "foobar", asTermLike "foobar", Test.Int.asInternal (-1)]
        (Test.Int.asPattern 0)
    , Test.Int.testInt
        "find after end of string"
        findStringSymbol
        [asTermLike "foobar", asTermLike "bar", Test.Int.asInternal 10]
        (Test.Int.asPattern (-1))
    , Test.Int.testInt
        "find pattern that does not exist"
        findStringSymbol
        [asTermLike "foobar", asTermLike "nope", Test.Int.asInternal 0]
        (Test.Int.asPattern (-1))
    ]

test_string2Base :: [TestTree]
test_string2Base =
    -- Decimal
    [ Test.Int.testInt
        "string2Base decimal simple"
        string2BaseStringSymbol
        [asTermLike "42", Test.Int.asInternal 10]
        (Test.Int.asPattern 42)
    , Test.Int.testInt
        "string2Base decimal negative"
        string2BaseStringSymbol
        [asTermLike "-42", Test.Int.asInternal 10]
        (Test.Int.asPattern (-42))
    , Test.Int.testInt
        "string2Base decimal is bottom"
        string2BaseStringSymbol
        [asTermLike "-42.3", Test.Int.asInternal 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal empty string is bottom"
        string2BaseStringSymbol
        [asTermLike "", Test.Int.asInternal 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal non-number is bottom"
        string2BaseStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 10]
        bottom
    , Test.Int.testInt
        "string2Base decimal from hex is bottom"
        string2BaseStringSymbol
        [asTermLike "baad", Test.Int.asInternal 10]
        bottom

    -- Octal
    , Test.Int.testInt
        "string2Base octal simple"
        string2BaseStringSymbol
        [asTermLike "42", Test.Int.asInternal 8]
        (Test.Int.asPattern 34)
    , Test.Int.testInt
        "string2Base octal negative is bottom"
        string2BaseStringSymbol
        [asTermLike "-42", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal is bottom"
        string2BaseStringSymbol
        [asTermLike "-42.3", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal empty string is bottom"
        string2BaseStringSymbol
        [asTermLike "", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal non-number is bottom"
        string2BaseStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 8]
        bottom
    , Test.Int.testInt
        "string2Base octal from hex is bottom"
        string2BaseStringSymbol
        [asTermLike "baad", Test.Int.asInternal 8]
        bottom

    -- Hexadecimal
    , Test.Int.testInt
        "string2Base hex simple"
        string2BaseStringSymbol
        [asTermLike "42", Test.Int.asInternal 16]
        (Test.Int.asPattern 66)
    , Test.Int.testInt
        "string2Base hex negative is bottom"
        string2BaseStringSymbol
        [asTermLike "-42", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex is bottom"
        string2BaseStringSymbol
        [asTermLike "-42.3", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex empty string is bottom"
        string2BaseStringSymbol
        [asTermLike "", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex non-number is bottom"
        string2BaseStringSymbol
        [asTermLike "foobar", Test.Int.asInternal 16]
        bottom
    , Test.Int.testInt
        "string2Base hex from hex is bottom"
        string2BaseStringSymbol
        [asTermLike "baad", Test.Int.asInternal 16]
        (Test.Int.asPattern 47789)
    ]

test_string2Int :: [TestTree]
test_string2Int =
    [ Test.Int.testInt
        "string2Base decimal simple"
        string2IntStringSymbol
        [asTermLike "42"]
        (Test.Int.asPattern 42)
    , Test.Int.testInt
        "string2Int decimal negative"
        string2IntStringSymbol
        [asTermLike "-42"]
        (Test.Int.asPattern (-42))
    , Test.Int.testInt
        "string2Int decimal is bottom"
        string2IntStringSymbol
        [asTermLike "-42.3"]
        bottom
    , Test.Int.testInt
        "string2Int decimal empty string is bottom"
        string2IntStringSymbol
        [asTermLike ""]
        bottom
    , Test.Int.testInt
        "string2Int decimal non-number is bottom"
        string2IntStringSymbol
        [asTermLike "foobar"]
        bottom
    , Test.Int.testInt
        "string2Int decimal from hex is bottom"
        string2IntStringSymbol
        [asTermLike "baad"]
        bottom
    ]

-- | Another name for asTermLike.
stringLiteral :: Text -> TermLike Variable
stringLiteral = asTermLike

-- | Specialize 'String.asTermLike' to the builtin sort 'stringSort'.
asTermLike :: Text -> TermLike Variable
asTermLike = String.asTermLike stringSort

-- | Specialize 'String.asConcretePattern' to the builtin sort 'stringSort'.
asConcretePattern :: Text -> TermLike Concrete
asConcretePattern = String.asConcretePattern stringSort

-- | Specialize 'String.asPattern' to the builtin sort 'stringSort'.
asPattern :: Text -> Pattern Variable
asPattern = String.asPattern stringSort

-- | Specialize 'String.asPartialPattern' to the builtin sort 'stringSort'.
asPartialPattern :: Maybe Text -> Pattern Variable
asPartialPattern = String.asPartialPattern stringSort

testString
    :: HasCallStack
    => String
    -> SymbolOrAlias
    -> [TermLike Variable]
    -> Pattern Variable
    -> TestTree
testString name = testSymbolWithSolver evaluate name stringSort
