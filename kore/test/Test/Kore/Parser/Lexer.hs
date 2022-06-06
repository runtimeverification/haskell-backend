module Test.Kore.Parser.Lexer (
    test_keyword,
    test_colon,
    test_comma,
    test_bracesPair,
    test_parseSymbolId,
    test_braces,
    test_parens,
    test_brackets,
    test_parseModuleName,
    test_parensTuple,
    test_parseStringLiteral,
    test_space,
) where

import Data.Text (
    Text,
 )
import Kore.Parser.Lexer
import Prelude.Kore
import Test.Kore.Parser
import Test.Tasty (
    TestTree,
 )

test_colon :: [TestTree]
test_colon =
    lexTree
        (successes [":", " :", ": ", ":/**/"] [TokenColon])

test_comma :: [TestTree]
test_comma =
    lexTree
        (successes [",", " ,", ", ", ",/**/"] [TokenComma])

test_bracesPair :: [TestTree]
test_bracesPair =
    lexTree
        ( successes
            [ "{a,B}"
            , " {a,B}"
            , "{ a , B } "
            , "{/**/a/**/,/**/B/**/}/**/"
            , "{/*/**/a,/**/B/**/}/**/"
            ]
            [ TokenLeftBrace
            , TokenIdent "a"
            , TokenComma
            , TokenIdent "B"
            , TokenRightBrace
            ]
            ++ [ success
                    "{a,b}"
                    [ TokenLeftBrace
                    , TokenIdent "a"
                    , TokenComma
                    , TokenIdent "b"
                    , TokenRightBrace
                    ]
               , success "{a}" [TokenLeftBrace, TokenIdent "a", TokenRightBrace]
               , success "{B}" [TokenLeftBrace, TokenIdent "B", TokenRightBrace]
               , success "{a,}" [TokenLeftBrace, TokenIdent "a", TokenComma, TokenRightBrace]
               , success "{,B}" [TokenLeftBrace, TokenComma, TokenIdent "B", TokenRightBrace]
               , success
                    "{a{},b}"
                    [ TokenLeftBrace
                    , TokenIdent "a"
                    , TokenLeftBrace
                    , TokenRightBrace
                    , TokenComma
                    , TokenIdent "b"
                    , TokenRightBrace
                    ]
               , success
                    "{a,B,c}"
                    [ TokenLeftBrace
                    , TokenIdent "a"
                    , TokenComma
                    , TokenIdent "B"
                    , TokenComma
                    , TokenIdent "c"
                    , TokenRightBrace
                    ]
               ]
        )

test_parseSymbolId :: [TestTree]
test_parseSymbolId =
    lexTree $
        mappend
            (successes ["a", "a ", " a", "a/**/ ", "//\na"] [TokenIdent "a"])
            [ success "A" [TokenIdent "A"]
            , success "abc" [TokenIdent "abc"]
            , success "a'" [TokenIdent "a'"]
            , success "a-" [TokenIdent "a-"]
            , success "a'2" [TokenIdent "a'2"]
            , success "\\something" [TokenIdent "\\something"]
            , success "[" [TokenLeftBracket]
            , success "module" [TokenModule]
            , FailureWithoutMessage
                [ "'"
                , "'a"
                , "2"
                , "2a"
                , "`"
                , "`a"
                , "#"
                , "#'"
                , "#'a"
                , "#2"
                , "#2a"
                , "#`"
                , "#`'"
                , "#`'a"
                , "#`2"
                , "#`2a"
                , "a#"
                ]
            ]

test_braces :: [TestTree]
test_braces =
    lexTree
        ( successes
            ["{a}", "{ a } ", "{/**/a/**/}/**/", " {a}"]
            [TokenLeftBrace, TokenIdent "a", TokenRightBrace]
            ++ [ success "{}" [TokenLeftBrace, TokenRightBrace]
               , success
                    "{a{}}"
                    [ TokenLeftBrace
                    , TokenIdent "a"
                    , TokenLeftBrace
                    , TokenRightBrace
                    , TokenRightBrace
                    ]
               , success "a}" [TokenIdent "a", TokenRightBrace]
               , success "{a" [TokenLeftBrace, TokenIdent "a"]
               ]
        )

test_parens :: [TestTree]
test_parens =
    lexTree
        ( successes
            ["(a)", "( a ) ", "(/**/a/**/)/**/", " (a)"]
            [TokenLeftParen, TokenIdent "a", TokenRightParen]
            ++ successes
                ["(a,B)", "( a , B ) ", "(/**/a/**/,/**/B/**/)/**/", " (a,B)"]
                [ TokenLeftParen
                , TokenIdent "a"
                , TokenComma
                , TokenIdent "B"
                , TokenRightParen
                ]
            ++ [ success "()" [TokenLeftParen, TokenRightParen]
               , success
                    "(a())"
                    [ TokenLeftParen
                    , TokenIdent "a"
                    , TokenLeftParen
                    , TokenRightParen
                    , TokenRightParen
                    ]
               , success "a)" [TokenIdent "a", TokenRightParen]
               , success "(a" [TokenLeftParen, TokenIdent "a"]
               , success "(B)" [TokenLeftParen, TokenIdent "B", TokenRightParen]
               , success
                    "(a,b)"
                    [ TokenLeftParen
                    , TokenIdent "a"
                    , TokenComma
                    , TokenIdent "b"
                    , TokenRightParen
                    ]
               ]
        )

test_brackets :: [TestTree]
test_brackets =
    lexTree
        ( successes
            ["[a]", "[ a ] ", "[/**/a/**/]/**/", " [a]"]
            [TokenLeftBracket, TokenIdent "a", TokenRightBracket]
            ++ [ success "[]" [TokenLeftBracket, TokenRightBracket]
               , success
                    "[a,b]"
                    [ TokenLeftBracket
                    , TokenIdent "a"
                    , TokenComma
                    , TokenIdent "b"
                    , TokenRightBracket
                    ]
               , success
                    "[a[]]"
                    [ TokenLeftBracket
                    , TokenIdent "a"
                    , TokenLeftBracket
                    , TokenRightBracket
                    , TokenRightBracket
                    ]
               , success "a]" [TokenIdent "a", TokenRightBracket]
               , success "[a" [TokenLeftBracket, TokenIdent "a"]
               ]
        )

test_keyword :: [TestTree]
test_keyword =
    lexTree
        ( successes ["hello", "hello ", "hello/**/ ", " hello"] [TokenIdent "hello"]
            ++ [ success "Hello" [TokenIdent "Hello"]
               , success "hello-world" [TokenIdent "hello-world"]
               ]
        )

test_parseModuleName :: [TestTree]
test_parseModuleName =
    lexTree $
        mappend
            (successes ["A", "A ", "A/**/ ", " A"] [TokenIdent "A"])
            [ success "A-" [TokenIdent "A-"]
            , success "A2" [TokenIdent "A2"]
            , success "a'-2" [TokenIdent "a'-2"]
            , FailureWithoutMessage
                [ "-"
                , "-A"
                , "2"
                , "2A"
                , "#"
                , "#A"
                ]
            ]

test_parensTuple :: [TestTree]
test_parensTuple =
    lexTree
        [ success "(a,)" [TokenLeftParen, TokenIdent "a", TokenComma, TokenRightParen]
        , success "(,B)" [TokenLeftParen, TokenComma, TokenIdent "B", TokenRightParen]
        , success
            "(a(),b)"
            [ TokenLeftParen
            , TokenIdent "a"
            , TokenLeftParen
            , TokenRightParen
            , TokenComma
            , TokenIdent "b"
            , TokenRightParen
            ]
        , success
            "(a,B,c)"
            [ TokenLeftParen
            , TokenIdent "a"
            , TokenComma
            , TokenIdent "B"
            , TokenComma
            , TokenIdent "c"
            , TokenRightParen
            ]
        ]

test_space :: [TestTree]
test_space =
    lexTree $
        mappend
            ( successes
                [ ""
                , " "
                , "\n"
                , "\r"
                , "\t"
                , "/**/"
                , "//\n"
                , "/*\n*/"
                , "/*//*/"
                , "/****/"
                , "/* * / */"
                , "/*/*/"
                , "//hello\n"
                , "//hello"
                , "\t//hello\n /* world\n //*/  //!\n"
                ]
                []
            )
            [ Failure
                FailureTest
                    { failureInput = "/*/"
                    , failureExpected =
                        "<test-string>:1:4: unexpected end of input\n"
                    }
            , FailureWithoutMessage
                [ "/*"
                , "/**"
                , "/***"
                , "/*hello"
                , "/*//"
                , "*/"
                , "/ /"
                , "/**//"
                ]
            ]

test_parseStringLiteral :: [TestTree]
test_parseStringLiteral =
    lexTree
        [ success "\"\"" [TokenString ""]
        , success "\"a\"" [TokenString "a"]
        , success "\"\\\"\"" [TokenString "\""]
        , success "\"\\f\"" [TokenString "\12"]
        , success "\"\\n\"" [TokenString "\10"]
        , success "\"\\r\"" [TokenString "\13"]
        , success "\"\\t\"" [TokenString "\9"]
        , success "\"\\u1ABC\"" [TokenString "\6844"]
        , success "\"\\u1ABCa\"" [TokenString $ "\6844" <> "a"]
        , success "\"\\u1abc\"" [TokenString "\6844"]
        , success "\"\\U000120FF\"" [TokenString "\73983"]
        , success "\"\\U000120FFa\"" [TokenString $ "\73983" <> "a"]
        , success "\"\\U000120ff\"" [TokenString "\73983"]
        , success "\"\\U0010FFFF\"" [TokenString "\1114111"]
        , success "\"\\xFF\"" [TokenString "\xFF"]
        , success "\"\\xff\"" [TokenString "\xFF"]
        , Failure
            FailureTest
                { failureInput = "\"\\xF\""
                , failureExpected =
                    "<test-string>:1:5: unexpected character '\"'\n"
                }
        , Failure
            FailureTest
                { failureInput = "\"\\xFr\""
                , failureExpected =
                    "<test-string>:1:5: unexpected character 'r'\n"
                }
        , invalidEscape "\"\\'\"" "\\'"
        , invalidEscape "\"\\b\"" "b"
        , invalidEscape "\"\\?\"" "?"
        , invalidEscape "\"\\a\"" "a"
        , invalidEscape "\"\\v\"" "v"
        , invalidEscape "\"\\377\"" "3"
        , invalidEscape "\"\\77\"" "7"
        , invalidEscape "\"\\77a\"" "7"
        , Failure
            FailureTest
                { failureInput = "\"\DEL\""
                , failureExpected =
                    "<test-string>:1:1: non-printable character '\\DEL' in string literal\n"
                }
        , Failure
            FailureTest
                { failureInput = "\"\\uD800\""
                , failureExpected =
                    "<test-string>:1:1: surrogate character '\\55296' in string literal\n"
                }
        , Failure
            FailureTest
                { failureInput = "\"\\uZZZZ\""
                , failureExpected =
                    "<test-string>:1:4: unexpected character 'Z'\n"
                }
        , Failure
            FailureTest
                { failureInput = "\"\\UFFFFFFFF\""
                , failureExpected =
                    "<test-string>:1:1: code point 4294967295 outside range of Unicode\n"
                }
        , FailureWithoutMessage
            [ "'a'"
            , "\"\\z\""
            , "\"\\xzf\""
            , "\"\\u123\""
            , "\"\\U1234567\""
            ]
        ]

invalidEscape :: Text -> String -> ParserTest a
invalidEscape failureInput nextChar =
    Failure FailureTest{failureInput, failureExpected}
  where
    failureExpected =
        "<test-string>:1:3: unexpected character '" ++ nextChar ++ "'\n"
