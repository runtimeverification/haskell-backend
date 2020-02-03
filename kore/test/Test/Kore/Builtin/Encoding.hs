module Test.Kore.Builtin.Encoding
    ( test_decodeEncode
    ) where

import Prelude.Kore

import Hedgehog hiding
    ( Concrete
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.Text
    ( Text
    )

import Kore.Builtin.Encoding

genString :: Gen Text
genString = Gen.text (Range.linear 0 256) Gen.latin1

test_decodeEncode :: TestTree
test_decodeEncode =
    testProperty "∀ t. decode (encode t) = t)" . property $ do
        str <- forAll genString
        (===) str (decode8Bit (encode8Bit str))
