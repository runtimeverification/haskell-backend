module Test.Kore.Builtin.Krypto where

import Hedgehog
import Test.Tasty

import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Valid
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.String as String
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.StepperAttributes

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.SMT

test_ecdsaRecover :: TestTree
test_ecdsaRecover =
    testPropertyWithSolver (Text.unpack name) $ do
        let expect = String.asExpandedPattern stringSort result
        actual <- evaluate $ mkApp stringSort ecdsaRecoverSymbol
            [ String.asPattern stringSort messageHash
            , Int.asPattern intSort 28
            , String.asPattern stringSort r
            , String.asPattern stringSort s
            ]
        (===) expect actual
  where
    StepperAttributes { hook = Hook { getHook = Just name } } =
        symAttributes testMetadataTools ecdsaRecoverSymbol

messageHash :: Text
messageHash =
    "!\\\159\132\149R\157\DLE\209[h\178\154J\242\190\SOH\218\235eK\SO.\194T_\192c\160\226\137O"

v :: Integer
v = 28

r :: Text
r =
    "\198R \210.\233S>i\202\f\202O-\144\219\171\208\219q\232h\131\221\167\154a5\168\150\198\194"

s :: Text
s =
    "\DC4\140\135*7X\219\&0\230\207\246=_\140\DC1U\189\241=\154\&9\191\153;B\211\242\204z\fV\138"

result :: Text
result =
    ":QAvFo\xa8\x15\xedH\x1f\xfa\xd0\x91\x10\xa2\xd3\&D\xf6\xc9\xb7\x8c\x1d\x14\xaf\xc3Q\xc3\xa5\x1b\xe3=\x80r\xe7y9\xdc\x03\xba\&Dy\x07y\xb7\xa1\x02[\xaf\&0\x03\xf6s$0\xe2\f\xd9\xb7m\x95\&3\x91\xb3"
