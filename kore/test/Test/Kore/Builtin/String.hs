module Test.Kore.Builtin.String where

import Hedgehog hiding
    ( Concrete
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty

import Data.Text
    ( Text
    )
import GHC.Stack
    ( HasCallStack
    )

import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.String as String
import Kore.Internal.Pattern
import Kore.Internal.TermLike

import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import Test.SMT

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
        "string2Base hex negative is bottom"
        string2BaseStringSymbol
        [asInternal "-42", Test.Int.asInternal 16]
        bottom
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
        "string2Base hex from hex is bottom"
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

-- | Another name for 'asInternal'.
stringLiteral :: Text -> TermLike Variable
stringLiteral = asInternal

-- | Specialize 'String.asInternal' to the builtin sort 'stringSort'.
asInternal :: Text -> TermLike Variable
asInternal = String.asInternal stringSort

-- | Specialize 'String.asPattern' to the builtin sort 'stringSort'.
asPattern :: Text -> Pattern Variable
asPattern = String.asPattern stringSort

-- | Specialize 'String.asPartialPattern' to the builtin sort 'stringSort'.
asPartialPattern :: Maybe Text -> Pattern Variable
asPartialPattern = String.asPartialPattern stringSort

testString
    :: HasCallStack
    => String
    -> Symbol
    -> [TermLike Variable]
    -> Pattern Variable
    -> TestTree
testString name = testSymbolWithSolver evaluate name
