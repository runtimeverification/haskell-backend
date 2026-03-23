module Test.Kore.Builtin.Float (
    test_domainValue,
    test_add,
    test_eq,
    test_precision,
    test_sign,
    test_int2float,
    test_float2int,
    test_float2string,
    test_string2float,
) where

import Data.Maybe (
    fromJust,
 )
import Data.Text (
    Text,
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.Float qualified as Float
import Kore.Internal.InternalFloat (
    FloatValue (..),
    InternalFloat (..),
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore
import Test.Kore.Builtin.Bool qualified as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.Int qualified as Test.Int
import Test.Kore.Builtin.String qualified as Test.String
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_domainValue :: TestTree
test_domainValue =
    testCase "FLOAT domain value verifies to InternalFloat" $
        case verifyPattern (Just floatSort) (Builtin.makeDomainValueTerm floatSort "0.5f") of
            Right (InternalFloat_ InternalFloat{internalFloatValue = Float32 _}) -> pure ()
            Right other ->
                assertFailure ("expected InternalFloat, got: " ++ show other)
            Left err ->
                assertFailure (show err)

test_add :: TestTree
test_add =
    testFloat
        "FLOAT.add 1.0f 2.0f"
        addFloatSymbol
        [asInternal "1.0f", asInternal "2.0f"]
        (asOrPattern "3.0f")

test_eq :: [TestTree]
test_eq =
    [ testBool
        "FLOAT.eq treats NaN as unequal"
        eqFloatSymbol
        [asInternal "NaNf", asInternal "NaNf"]
        (Test.Bool.asOrPattern False)
    , testBool
        "FLOAT.eq treats signed zeros as equal"
        eqFloatSymbol
        [asInternal "0.0f", asInternal "-0.0f"]
        (Test.Bool.asOrPattern True)
    ]

test_precision :: TestTree
test_precision =
    Test.Int.testInt
        "FLOAT.precision on binary32"
        precisionFloatSymbol
        [asInternal "1.0f"]
        (Test.Int.asOrPattern 24)

test_sign :: [TestTree]
test_sign =
    [ testBool
        "FLOAT.sign sees negative zero"
        signFloatSymbol
        [asInternal "-0.0f"]
        (Test.Bool.asOrPattern True)
    , testBool
        "FLOAT.sign sees positive zero"
        signFloatSymbol
        [asInternal "0.0f"]
        (Test.Bool.asOrPattern False)
    ]

test_int2float :: TestTree
test_int2float =
    testFloat
        "FLOAT.int2float produces binary32"
        int2FloatSymbol
        [Test.Int.asInternal 7, Test.Int.asInternal 24, Test.Int.asInternal 8]
        (asOrPattern "7.0f")

test_float2int :: TestTree
test_float2int =
    Test.Int.testInt
        "FLOAT.float2int rounds ties to even"
        float2IntSymbol
        [asInternal "2.5"]
        (Test.Int.asOrPattern 2)

test_float2string :: TestTree
test_float2string =
    testSymbolWithoutSolver
        evaluateTerm
        "STRING.float2string preserves concrete float syntax"
        float2StringSymbol
        [asInternal "1.5f"]
        (Test.String.asOrPattern "1.5f")

test_string2float :: TestTree
test_string2float =
    testFloat
        "STRING.string2float parses IEEE syntax"
        string2FloatSymbol
        [Test.String.asInternal "1.5f"]
        (asOrPattern "1.5f")

asInternal :: Text -> TermLike variable
asInternal =
    Float.asInternal floatSort
        . fromJust
        . Float.parseText

asPattern :: Text -> Pattern RewritingVariableName
asPattern =
    Float.asPattern floatSort
        . fromJust
        . Float.parseText

asOrPattern :: Text -> OrPattern RewritingVariableName
asOrPattern = MultiOr.singleton . asPattern

testFloat ::
    HasCallStack =>
    String ->
    Symbol ->
    [TermLike RewritingVariableName] ->
    OrPattern RewritingVariableName ->
    TestTree
testFloat name = testSymbolWithoutSolver evaluateTerm name

testBool ::
    HasCallStack =>
    String ->
    Symbol ->
    [TermLike RewritingVariableName] ->
    OrPattern RewritingVariableName ->
    TestTree
testBool name = testSymbolWithoutSolver evaluateTerm name
