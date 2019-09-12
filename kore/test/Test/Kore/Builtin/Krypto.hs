module Test.Kore.Builtin.Krypto where

import Hedgehog
import Test.Tasty

import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.String as String
import Kore.Internal.TermLike

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import Test.SMT

testKeyRecover :: Text -> Integer -> Text -> Text -> Text -> TestTree
testKeyRecover messageHash v r s result =
    testPropertyWithSolver (Text.unpack name) $ do
        let expect = String.asPattern stringSort result
        actual <- evaluateT $ mkApplySymbol ecdsaRecoverSymbol
                    [ String.asInternal stringSort messageHash
                    , Test.Int.asInternal v
                    , String.asInternal stringSort r
                    , String.asInternal stringSort s
                    ]
        (===) expect actual
  where
    Just name =
        Attribute.getHook . Attribute.hook $ symbolAttributes ecdsaRecoverSymbol

testKeccak :: Text -> Text -> TestTree
testKeccak input result =
    testPropertyWithSolver (Text.unpack name) $ do
        let expect = String.asPattern stringSort result
        actual <- evaluateT $ mkApplySymbol keccakSymbol
                    [ String.asInternal stringSort input ]
        (===) expect actual
  where
    Just name =
        Attribute.getHook . Attribute.hook $ symbolAttributes ecdsaRecoverSymbol

test_ecdsaRecover :: [TestTree]
test_ecdsaRecover =
    [ testKeyRecover
        "!\\\159\132\149R\157\DLE\209[h\178\154J\242\190\SOH\218\235eK\SO.\194T_\192c\160\226\137O"
        28
        "\198R \210.\233S>i\202\f\202O-\144\219\171\208\219q\232h\131\221\167\154a5\168\150\198\194"
        "\DC4\140\135*7X\219\&0\230\207\246=_\140\DC1U\189\241=\154\&9\191\153;B\211\242\204z\fV\138"
        ":QAvFo\xa8\x15\xedH\x1f\xfa\xd0\x91\x10\xa2\xd3\&D\xf6\xc9\xb7\x8c\x1d\x14\xaf\xc3Q\xc3\xa5\x1b\xe3=\x80r\xe7y9\xdc\x03\xba\&Dy\x07y\xb7\xa1\x02[\xaf\&0\x03\xf6s$0\xe2\f\xd9\xb7m\x95\&3\x91\xb3"
    , testKeyRecover
        "g\r\130\153\229\171\230\224\156\SYN\STX\181\SIxa9\163\129\FSy\SUB8\206\&7\162\&8\191a\199\171\143\155"
        27
        "\152\137\DC2m\159\r\208\135P\EOT\CAN\178\229\SO\172f\142O\155\143*{\145j\DC3\251\GS\144)6\f\139"
        "{:\168JZ\211\159\223\228\&6\211\205\GS\165@@\190w#\SOe\209q4p\249XlE\180\217\139"
        "\214q\EOT\230[a\252\161\252s\167Auf|\DC1\241l\ETX\DEL\168\228\DC4I\145\137\223\157hpj\202n\SUB\ESCN\160+p/\DLE\RS\182\t\196\205)d\212y\NULG\160dX\186\138\SUB\EM\EOT\n\177\254\r"
    ]

test_keccak256 :: [TestTree]
test_keccak256 =
    [ testKeccak
         "\249\SOH\245\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\160\GS\204M\232\222\199]z\171\133\181g\182\204\212\SUB\211\DC2E\ESC\148\138t\DC3\240\161B\253@\212\147G\148*\220%fP\CAN\170\US\224\230\188fm\172\143\194i\DEL\249\186\160h\172|e\163\163\ESC}\139\230!\217\157/\"w\SOHX]\232s\219\218\162\181\248\215K\225Z\241\178\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\185\SOH\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\131\STX\NUL\NUL\128\131\SIB@\128\130\ETX\182B\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\136\SOH\STX\ETX\EOT\ENQ\ACK\a\b"
        "417ece6e4175ae7f1bf6b8ed90b4ea22206353a7450aa10bdd5e2ba3cb2bd953"
    ]
