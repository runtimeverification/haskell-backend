module Test.Kore.Builtin.Encoding where

import qualified Data.ByteString.Char8 as BS
import Hedgehog hiding
    ( Concrete
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.ByteString
    ( ByteString
    )
import Data.Char
    ( ord
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as T
import GHC.Stack
    ( HasCallStack
    )

import Kore.Builtin.Encoding
import Kore.Internal.Pattern
import Kore.Internal.TermLike hiding
    ( bytesSort
    )

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.String as Test.String
import Test.SMT


genString :: Gen Text
genString = Gen.text (Range.linear 0 256) Gen.latin1

test_decodeEncode :: TestTree
test_decodeEncode =
    testProperty "∀ t. decode (encode t) = t)" . property $ do
        str <- forAll genString
        (===) str (decode8Bit (encode8Bit str))
