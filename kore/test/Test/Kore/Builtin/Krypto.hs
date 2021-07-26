{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Builtin.Krypto (
    test_ecdsaRecover,
    test_secp256k1EcdsaRecover,
    test_keccak256,
    test_hashKeccak256,
    test_sha256,
    test_hashSha256,
    test_sha3256,
    test_hashSha3_256,
    test_ripemd160,
    test_hashRipemd160,
) where

import qualified Control.Lens as Lens
import Data.Generics.Sum.Constructors
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified GHC.TypeLits as TypeLits
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Krypto as Krypto
import qualified Kore.Builtin.String as String
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Data (
    runSimplifier,
 )
import Kore.Simplify.Simplify (
    AttemptedAxiomResults (..),
    BuiltinAndAxiomSimplifier (..),
 )
import qualified Kore.TopBottom as TopBottom
import Prelude.Kore
import Test.Kore.Builtin.Builtin hiding (
    evaluate,
 )
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import Test.SMT (
    runNoSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_ecdsaRecover :: [TestTree]
test_ecdsaRecover =
    [ test
        "!\\\159\132\149R\157\DLE\209[h\178\154J\242\190\SOH\218\235eK\SO.\194T_\192c\160\226\137O"
        28
        "\198R \210.\233S>i\202\f\202O-\144\219\171\208\219q\232h\131\221\167\154a5\168\150\198\194"
        "\DC4\140\135*7X\219\&0\230\207\246=_\140\DC1U\189\241=\154\&9\191\153;B\211\242\204z\fV\138"
        ":QAvFo\xa8\x15\xedH\x1f\xfa\xd0\x91\x10\xa2\xd3\&D\xf6\xc9\xb7\x8c\x1d\x14\xaf\xc3Q\xc3\xa5\x1b\xe3=\x80r\xe7y9\xdc\x03\xba\&Dy\x07y\xb7\xa1\x02[\xaf\&0\x03\xf6s$0\xe2\f\xd9\xb7m\x95\&3\x91\xb3"
    , test
        "g\r\130\153\229\171\230\224\156\SYN\STX\181\SIxa9\163\129\FSy\SUB8\206\&7\162\&8\191a\199\171\143\155"
        27
        "\152\137\DC2m\159\r\208\135P\EOT\CAN\178\229\SO\172f\142O\155\143*{\145j\DC3\251\GS\144)6\f\139"
        "{:\168JZ\211\159\223\228\&6\211\205\GS\165@@\190w#\SOe\209q4p\249XlE\180\217\139"
        "\214q\EOT\230[a\252\161\252s\167Auf|\DC1\241l\ETX\DEL\168\228\DC4I\145\137\223\157hpj\202n\SUB\ESCN\160+p/\DLE\RS\182\t\196\205)d\212y\NULG\160dX\186\138\SUB\EM\EOT\n\177\254\r"
    ]
  where
    test messageHash v r s result =
        testCase (Text.unpack name) $ do
            let expect = String.asPattern stringSort result
            actual <-
                ecdsaRecoverKrypto
                    (String.asInternal stringSort messageHash)
                    (Test.Int.asInternal v)
                    (String.asInternal stringSort r)
                    (String.asInternal stringSort s)
                    & evaluate "KRYPTO.ecdsaRecover"
            assertEqual "" expect actual
      where
        Just name =
            Attribute.getHook . Attribute.hook $
                symbolAttributes ecdsaRecoverSymbol

test_secp256k1EcdsaRecover :: [TestTree]
test_secp256k1EcdsaRecover =
    [ test
        "!\\\159\132\149R\157\DLE\209[h\178\154J\242\190\SOH\218\235eK\SO.\194T_\192c\160\226\137O"
        28
        "\198R \210.\233S>i\202\f\202O-\144\219\171\208\219q\232h\131\221\167\154a5\168\150\198\194"
        "\DC4\140\135*7X\219\&0\230\207\246=_\140\DC1U\189\241=\154\&9\191\153;B\211\242\204z\fV\138"
        ":QAvFo\xa8\x15\xedH\x1f\xfa\xd0\x91\x10\xa2\xd3\&D\xf6\xc9\xb7\x8c\x1d\x14\xaf\xc3Q\xc3\xa5\x1b\xe3=\x80r\xe7y9\xdc\x03\xba\&Dy\x07y\xb7\xa1\x02[\xaf\&0\x03\xf6s$0\xe2\f\xd9\xb7m\x95\&3\x91\xb3"
    , test
        "g\r\130\153\229\171\230\224\156\SYN\STX\181\SIxa9\163\129\FSy\SUB8\206\&7\162\&8\191a\199\171\143\155"
        27
        "\152\137\DC2m\159\r\208\135P\EOT\CAN\178\229\SO\172f\142O\155\143*{\145j\DC3\251\GS\144)6\f\139"
        "{:\168JZ\211\159\223\228\&6\211\205\GS\165@@\190w#\SOe\209q4p\249XlE\180\217\139"
        "\214q\EOT\230[a\252\161\252s\167Auf|\DC1\241l\ETX\DEL\168\228\DC4I\145\137\223\157hpj\202n\SUB\ESCN\160+p/\DLE\RS\182\t\196\205)d\212y\NULG\160dX\186\138\SUB\EM\EOT\n\177\254\r"
    ]
  where
    test messageHash v r s result =
        testCase (Text.unpack name) $ do
            let expect = String.asPattern stringSort result
            actual <-
                ecdsaRecoverKrypto
                    (String.asInternal stringSort messageHash)
                    (Test.Int.asInternal v)
                    (String.asInternal stringSort r)
                    (String.asInternal stringSort s)
                    & evaluate "SECP256K1.ecdsaRecover"
            assertEqual "" expect actual
      where
        Just name =
            Attribute.getHook . Attribute.hook $
                symbolAttributes ecdsaRecoverSymbol

test_keccak256 :: [TestTree]
test_keccak256 =
    [ test
        "\249\SOH\245\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\160\GS\204M\232\222\199]z\171\133\181g\182\204\212\SUB\211\DC2E\ESC\148\138t\DC3\240\161B\253@\212\147G\148*\220%fP\CAN\170\US\224\230\188fm\172\143\194i\DEL\249\186\160h\172|e\163\163\ESC}\139\230!\217\157/\"w\SOHX]\232s\219\218\162\181\248\215K\225Z\241\178\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\185\SOH\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\131\STX\NUL\NUL\128\131\SIB@\128\130\ETX\182B\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\136\SOH\STX\ETX\EOT\ENQ\ACK\a\b"
        "417ece6e4175ae7f1bf6b8ed90b4ea22206353a7450aa10bdd5e2ba3cb2bd953"
    , -- from the frontend's test suite:
      test
        "testing"
        "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                keccak256Krypto (String.asInternal stringSort input)
                    & evaluate "KRYPTO.keccak256"
            assertEqual "" expect actual

test_hashKeccak256 :: [TestTree]
test_hashKeccak256 =
    [ test
        "\249\SOH\245\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\160\GS\204M\232\222\199]z\171\133\181g\182\204\212\SUB\211\DC2E\ESC\148\138t\DC3\240\161B\253@\212\147G\148*\220%fP\CAN\170\US\224\230\188fm\172\143\194i\DEL\249\186\160h\172|e\163\163\ESC}\139\230!\217\157/\"w\SOHX]\232s\219\218\162\181\248\215K\225Z\241\178\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\185\SOH\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\131\STX\NUL\NUL\128\131\SIB@\128\130\ETX\182B\160V\232\US\ETB\ESC\204U\166\255\131E\230\146\192\248n[H\224\ESC\153l\173\192\SOHb/\181\227c\180!\136\SOH\STX\ETX\EOT\ENQ\ACK\a\b"
        "417ece6e4175ae7f1bf6b8ed90b4ea22206353a7450aa10bdd5e2ba3cb2bd953"
    , -- from the frontend's test suite:
      test
        "testing"
        "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                keccak256Krypto (String.asInternal stringSort input)
                    & evaluate "HASH.keccak256"
            assertEqual "" expect actual

test_sha256 :: [TestTree]
test_sha256 =
    -- from the NIST conformance tests:
    [ test
        ""
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    , test
        "\xd3"
        "28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                sha256Krypto (String.asInternal stringSort input)
                    & evaluate "KRYPTO.sha256"
            assertEqual "" expect actual

test_hashSha256 :: [TestTree]
test_hashSha256 =
    -- from the NIST conformance tests:
    [ test
        ""
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    , test
        "\xd3"
        "28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                sha256Krypto (String.asInternal stringSort input)
                    & evaluate "HASH.sha256"
            assertEqual "" expect actual

test_sha3256 :: [TestTree]
test_sha3256 =
    -- from the NIST conformance tests:
    [ test
        ""
        "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
    , test
        "\xe9"
        "f0d04dd1e6cfc29a4460d521796852f25d9ef8d28b44ee91ff5b759d72c1e6d6"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                sha3256Krypto (String.asInternal stringSort input)
                    & evaluate "KRYPTO.sha3256"
            assertEqual "" expect actual

test_hashSha3_256 :: [TestTree]
test_hashSha3_256 =
    -- from the NIST conformance tests:
    [ test
        ""
        "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
    , test
        "\xe9"
        "f0d04dd1e6cfc29a4460d521796852f25d9ef8d28b44ee91ff5b759d72c1e6d6"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                sha3256Krypto (String.asInternal stringSort input)
                    & evaluate "HASH.sha3_256"
            assertEqual "" expect actual

test_ripemd160 :: [TestTree]
test_ripemd160 =
    -- from the frontend test suite:
    [ test
        ""
        "9c1185a5c5e9fc54612808977ee8f548b2258d31"
    , test
        "a"
        "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
    , test
        "abc"
        "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
    , test
        "message digest"
        "5d0689ef49d2fae572b881b123a85ffa21595f36"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                ripemd160Krypto (String.asInternal stringSort input)
                    & evaluate "KRYPTO.ripemd160"
            assertEqual "" expect actual

test_hashRipemd160 :: [TestTree]
test_hashRipemd160 =
    -- from the frontend test suite:
    [ test
        ""
        "9c1185a5c5e9fc54612808977ee8f548b2258d31"
    , test
        "a"
        "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
    , test
        "abc"
        "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
    , test
        "message digest"
        "5d0689ef49d2fae572b881b123a85ffa21595f36"
    ]
  where
    test input result =
        testCase (show input) $ do
            let expect = String.asPattern stringSort result
            actual <-
                ripemd160Krypto (String.asInternal stringSort input)
                    & evaluate "HASH.ripemd160"
            assertEqual "" expect actual

evaluate ::
    Text ->
    TermLike RewritingVariableName ->
    IO (Pattern RewritingVariableName)
evaluate builtin termLike = do
    evaluator <-
        Map.lookup builtin Krypto.builtinFunctions
            & expectConstructor @"Just"
    attempt <-
        runBuiltinAndAxiomSimplifier evaluator termLike SideCondition.top
            & runSimplifier testEnv
            & runNoSMT
    attemptResults <- expectConstructor @"Applied" attempt
    let AttemptedAxiomResults{results, remainders} = attemptResults
    assertBool "Expected no remainders" $ TopBottom.isBottom remainders
    case OrPattern.toPatterns results of
        [actual] -> return actual
        _ -> assertFailure "Expected one result"

expectConstructor ::
    forall (ctor :: TypeLits.Symbol) s a.
    (AsConstructor' ctor s a, TypeLits.KnownSymbol ctor) =>
    HasCallStack =>
    (s -> IO a)
expectConstructor s =
    Lens.preview (_Ctor' @ctor) s
        & maybe failure return
  where
    failure = assertFailure ("Expected " ++ TypeLits.symbolVal (Proxy @ctor))
