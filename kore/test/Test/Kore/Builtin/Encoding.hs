module Test.Kore.Builtin.Encoding (
    test_decodeEncode,
    test_parseBase16,
) where

import qualified Data.ByteString as ByteString
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Data.Word (
    Word8,
 )
import Hedgehog hiding (
    Concrete,
 )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Kore.Builtin.Encoding
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Tasty.Hedgehog
import qualified Text.Megaparsec as Parsec

genString :: Gen Text
genString = Gen.text (Range.linear 0 256) Gen.latin1

test_decodeEncode :: TestTree
test_decodeEncode =
    testProperty "∀ t. decode (encode t) = t)" . property $ do
        str <- forAll genString
        (===) str (decode8Bit (encode8Bit str))

test_parseBase16 :: [TestTree]
test_parseBase16 =
    [ valid "" []
    , valid "00" [0x00]
    , valid "ff" [0xff]
    , invalid "0"
    , invalid "fg"
    ]
  where
    valid :: HasCallStack => String -> [Word8] -> TestTree
    valid (Text.pack -> input) (ByteString.pack -> expect) =
        testCase ("parseBase16 " <> show input) $
            either unexpected expected $
                Parsec.parse parseBase16 "<test>" input
      where
        unexpected = error . Parsec.errorBundlePretty
        expected = assertEqual "" expect

    invalid :: HasCallStack => String -> TestTree
    invalid (Text.pack -> input) =
        testCase ("parseBase16 " <> show input) $ do
            let result = Parsec.parse parseBase16 "<test>" input
            assertBool "expected parse error" (isLeft result)
