module Test.Kore.Builtin.Bytes.Bytes where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Maybe
    ( fromJust
    )
import qualified Data.Sequence as Seq
import Data.Word
    ( Word8
    )

import Kore.Builtin.Bytes.Bytes

import Test.Kore.Builtin.Definition

string2bytes :: String -> Internal
string2bytes = fromJust . string2bytesInternal string2bytesSymbol

replicate' :: Int -> Word8 -> Maybe Internal
replicate' = replicateInternal string2bytesSymbol

fromChar' :: Char -> Word8
fromChar' = fromJust . fromChar

test_lengthInternal :: [TestTree]
test_lengthInternal =
    [ test ""    0
    , test "abc" 3
    ]
  where
    test inp expect =
        testCase (show inp)
        $ assertEqual "" expect $ lengthInternal (string2bytes inp)

test_getInternal :: [TestTree]
test_getInternal =
    [ test (""        , 0) Nothing
    , test ("\x40"    , 0) (Just 0x40)
    , test ("\x40"    , 1) Nothing
    , test ("\x40\x41", 0) (Just 0x40)
    , test ("\x40\x41", 1) (Just 0x41)
    ]
  where
    test args@(inp, off) expect =
        testCase (show args)
        $ assertEqual "" expect $ getInternal (string2bytes inp) off

test_replicateInternal :: [TestTree]
test_replicateInternal =
    [ test (-1, 0x40) Nothing
    , test ( 0, 0x40) (Just "")
    , test ( 1, 0x40) (Just "\x40")
    , test ( 2, 0x40) (Just "\x40\x40")
    ]
  where
    test args@(len, byt) out =
        testCase (show args) $ do
            let expect = string2bytes <$> out
                actual = replicate' len byt
            assertEqual "" expect actual

test_fromChar :: [TestTree]
test_fromChar =
    test '\x100' Nothing
    : zipWith test ['\x00'..'\xFF'] (Just <$> [0x00..0xFF])
  where
    test inp expect =
        testCase (show inp) $ assertEqual "" expect (fromChar inp)

test_string2bytesInternal :: [TestTree]
test_string2bytesInternal =
    [ testCase "string2bytes(\"\x100\")"
        $ string2bytesInternal string2bytesSymbol "\x100" @?= Nothing
    ]

test_updateInternal :: [TestTree]
test_updateInternal =
    [ test ("abc", -1, 'd') Nothing
    , test ("abc",  2, 'd') (Just "abd")
    , test ("abc",  3, 'd') Nothing
    ]
  where
    test args@(inp, off, byt) out =
        testCase (show args) $ do
            let expect = string2bytes <$> out
                actual = updateInternal (string2bytes inp) off (fromChar' byt)
            assertEqual "" expect actual

test_substrInternal :: [TestTree]
test_substrInternal =
    [ test ("abcdef",  0,  3) (Just "abc")
    , test ("abcdef",  3,  3) (Just "def")
    , test ("abcdef",  3, -1) Nothing
    , test ("abcdef",  3,  4) Nothing
    , test ("abcdef", -1,  3) Nothing
    , test ("abcdef",  6,  1) Nothing
    , test ("abcdef",  6,  0) (Just "")
    ]
  where
    test args@(inp, off, len) out =
        testCase (show args) $ do
            let expect = string2bytes <$> out
                actual = substrInternal (string2bytes inp) off len
            assertEqual "" expect actual

test_replaceAtInternal :: [TestTree]
test_replaceAtInternal =
    [ test ("abcdef",  0, "ghi") (Just "ghidef")
    , test ("abcdef",  1, "ghi") (Just "aghief")
    , test ("abcdef",  2, "ghi") (Just "abghif")
    , test ("abcdef",  3, "ghi") (Just "abcghi")
    , test ("abcdef",  4, "ghi") Nothing
    , test ("abcdef", -1, "ghi") Nothing
    ]
  where
    test args@(inp, off, rpl) out =
        testCase (show args) $ do
            let expect = string2bytes <$> out
                actual =
                    replaceAtInternal (string2bytes inp) off (string2bytes rpl)
            assertEqual "" expect actual

test_padRightInternal :: [TestTree]
test_padRightInternal =
    [ test ("abc",  0, 'd') (Just "abc")
    , test ("abc", -1, 'd') Nothing
    , test ("abc",  2, 'd') (Just "abcdd")
    ]
  where
    test args@(inp, off, byt) out =
        testCase (show args) $ do
            let expect = string2bytes <$> out
                actual = padRightInternal (string2bytes inp) off (fromChar' byt)
            assertEqual "" expect actual

test_padLeftInternal :: [TestTree]
test_padLeftInternal =
    [ test ("abc",  0, 'd') (Just "abc")
    , test ("abc", -1, 'd') Nothing
    , test ("abc",  2, 'd') (Just "ddabc")
    ]
  where
    test args@(inp, off, byt) out =
        testCase (show args) $ do
            let expect = string2bytes <$> out
                actual = padLeftInternal (string2bytes inp) off (fromChar' byt)
            assertEqual "" expect actual

test_reverseInternal :: [TestTree]
test_reverseInternal =
    [ test "abc" "cba"
    , test "aaa" "aaa"
    , test ""    ""
    ]
  where
    test inp out =
        testCase (show inp) $ do
            let expect = string2bytes out
                actual = reverseInternal (string2bytes inp)
            assertEqual "" expect actual

test_concatInternal :: [TestTree]
test_concatInternal =
    [ test ("", [], "") ""

    , test ("abc", [     ],    "") "abc"
    , test (   "", [     ], "abc") "abc"
    , test (   "", ["abc"],    "") "abc"

    , test ("abc", ["def"       ],    "") "abcdef"
    , test ("abc", [            ], "def") "abcdef"
    , test (   "", ["abc", "def"],    "") "abcdef"
    , test (   "", ["abc"       ], "def") "abcdef"

    , test ("abc", ["def", "ghi"],    "") "abcdefghi"
    , test ("abc", ["def"       ], "ghi") "abcdefghi"
    , test (   "", ["abc", "def"], "ghi") "abcdefghi"
    ]
  where
    test args@(inp1, inpI, inpN) out =
        testCase (show args) $ do
            let expect = string2bytes out
                actual =
                    concatInternal
                        (string2bytes inp1)
                        (Seq.fromList $ string2bytes <$> inpI)
                        (string2bytes inpN)
            assertEqual "" expect actual
