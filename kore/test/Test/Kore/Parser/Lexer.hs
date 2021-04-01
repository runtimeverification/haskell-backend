{-# LANGUAGE Strict #-}
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
    unpack,
 )
import Kore.Parser.Lexer
import Kore.Syntax.Definition
import Kore.Syntax.StringLiteral
import Prelude.Kore
import Test.Kore
import Test.Kore.Parser
import Test.Tasty (
    TestTree,
 )

test_colon :: [TestTree]
test_colon =
    parseSkipTree
        colon
        [ Skip [":", ": ", ":/**/"]
        , FailureWithoutMessage ["", " :", " ", ","]
        ]

test_comma :: [TestTree]
test_comma =
    parseSkipTree
        comma
        [ Skip [",", ", ", ",/**/"]
        , FailureWithoutMessage ["", " ,", " ", ":"]
        ]

test_bracesPair :: [TestTree]
test_bracesPair =
    parseTree
        (bracesPair parseId)
        [ success "{a,B}" (testId "a", testId "B")
        , success "{ a , B } " (testId "a", testId "B")
        , success "{/**/a/**/,/**/B/**/}/**/" (testId "a", testId "B")
        , success "{/*/**/a,/**/B/**/}/**/" (testId "a", testId "B")
        , FailureWithoutMessage
            [ ""
            , " {a,B}"
            , "{a}"
            , "{B}"
            , "{a,}"
            , "{,B}"
            , "{a{},b}"
            , "{a,B,c}"
            , "(a,B)"
            ]
        ]

test_parseSymbolId :: [TestTree]
test_parseSymbolId =
    parseTree
        parseSymbolId
        [ success "A" (testId "A")
        , success "a" (testId "a")
        , success "abc" (testId "abc")
        , success "a'" (testId "a'")
        , success "a-" (testId "a-")
        , success "a'2" (testId "a'2")
        , success "a " (testId "a")
        , success "a/**/ " (testId "a")
        , success "\\something" (testId "\\something")
        , Failure
            FailureTest
                { failureInput = "["
                , failureExpected =
                    "<test-string>:1:1:\n\
                    \  |\n\
                    \1 | [\n\
                    \  | ^\n\
                    \unexpected '['\n\
                    \expecting symbol or alias identifier\n"
                }
        , Failure
            FailureTest
                { failureInput = "module"
                , failureExpected =
                    "<test-string>:1:7:\n\
                    \  |\n\
                    \1 | module\n\
                    \  |       ^\n\
                    \Identifiers should not be keywords: 'module'.\n"
                }
        , FailureWithoutMessage
            [ ""
            , "'"
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
            , ","
            , " a"
            ]
        ]

test_braces :: [TestTree]
test_braces =
    parseTree
        (braces parseId)
        [ success "{a}" (testId "a")
        , success "{ a } " (testId "a")
        , success "{/**/a/**/}/**/" (testId "a")
        , FailureWithoutMessage
            ["", "{}", " {a}", "{a,b}", "{a{}}", "a}", "{a"]
        ]

test_parens :: [TestTree]
test_parens =
    parseTree
        (parens parseId)
        [ success "(a)" (testId "a")
        , success "( a ) " (testId "a")
        , success "(/**/a/**/)/**/" (testId "a")
        , FailureWithoutMessage
            ["", "()", " (a)", "(a,b)", "(a())", "a)", "(a"]
        ]

test_brackets :: [TestTree]
test_brackets =
    parseTree
        (brackets parseId)
        [ success "[a]" (testId "a")
        , success "[ a ] " (testId "a")
        , success "[/**/a/**/]/**/" (testId "a")
        , FailureWithoutMessage
            ["", "[]", " [a]", "[a,b]", "[a[]]", "a]", "[a"]
        ]

test_keyword :: [TestTree]
test_keyword =
    parseSkipTree
        (keyword "hello")
        [ Skip ["hello", "hello ", "hello/**/ "]
        , FailureWithoutMessage ["", "Hello", " hello", "hello-world"]
        ]

test_parseModuleName :: [TestTree]
test_parseModuleName =
    parseTree
        parseModuleName
        [ success "A" (ModuleName "A")
        , success "A-" (ModuleName "A-")
        , success "A2" (ModuleName "A2")
        , success "a'-2" (ModuleName "a'-2")
        , success "A " (ModuleName "A")
        , success "A/**/ " (ModuleName "A")
        , FailureWithoutMessage
            [ ""
            , "-"
            , "-A"
            , "2"
            , "2A"
            , "#"
            , "#A"
            , " A"
            , ","
            ]
        ]

test_parensTuple :: [TestTree]
test_parensTuple =
    parseTree
        (parensTuple parseId parseModuleName)
        [ success "(a,B)" (testId "a", ModuleName "B")
        , success "( a , B ) " (testId "a", ModuleName "B")
        , success "(/**/a/**/,/**/B/**/)/**/" (testId "a", ModuleName "B")
        , FailureWithoutMessage
            [ ""
            , " (a,B)"
            , "(a)"
            , "(B)"
            , "(a,)"
            , "(,B)"
            , "(a(),b)"
            , "(a,B,c)"
            , "{a,B}"
            ]
        ]

test_space :: [TestTree]
test_space =
    parseSkipTree
        space
        [ Skip
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
        , Failure
            FailureTest
                { failureInput = "/*/"
                , failureExpected =
                    "<test-string>:1:4:\n\
                    \  |\n\
                    \1 | /*/\n\
                    \  |    ^\n\
                    \unexpected end of input\n\
                    \expecting \"*/\"\n"
                }
        , FailureWithoutMessage
            [ "a"
            , "/*"
            , "/**"
            , "/***"
            , "/*hello"
            , "/*//"
            , "*/"
            , "/ /"
            , "/**//"
            , "//\na"
            ]
        ]

test_parseStringLiteral :: [TestTree]
test_parseStringLiteral =
    parseTree
        parseStringLiteral
        [ success "\"\"" (StringLiteral "")
        , success "\"a\"" (StringLiteral "a")
        , success "\"\\\"\"" (StringLiteral "\"")
        , success "\"\\f\"" (StringLiteral "\12")
        , success "\"\\n\"" (StringLiteral "\10")
        , success "\"\\r\"" (StringLiteral "\13")
        , success "\"\\t\"" (StringLiteral "\9")
        , success "\"\\u1ABC\"" (StringLiteral "\6844")
        , success "\"\\u1ABCa\"" (StringLiteral ("\6844" <> "a"))
        , success "\"\\u1abc\"" (StringLiteral "\6844")
        , success "\"\\U000120FF\"" (StringLiteral "\73983")
        , success "\"\\U000120FFa\"" (StringLiteral ("\73983" <> "a"))
        , success "\"\\U000120ff\"" (StringLiteral "\73983")
        , success "\"\\xFF\"" (StringLiteral "\xFF")
        , success "\"\\xff\"" (StringLiteral "\xFF")
        , Failure
            FailureTest
                { failureInput = "\"\\xF\""
                , failureExpected =
                    unlines
                        [ "<test-string>:1:5:"
                        , "  |"
                        , "1 | \"\\xF\""
                        , "  |     ^"
                        , "unexpected '\"'"
                        , "expecting hexadecimal digit"
                        ]
                }
        , Failure
            FailureTest
                { failureInput = "\"\\xFr\""
                , failureExpected =
                    unlines
                        [ "<test-string>:1:5:"
                        , "  |"
                        , "1 | \"\\xFr\""
                        , "  |     ^"
                        , "unexpected 'r'"
                        , "expecting hexadecimal digit"
                        ]
                }
        , invalidEscape "\"\\'\""
        , invalidEscape "\"\\b\""
        , invalidEscape "\"\\?\""
        , invalidEscape "\"\\a\""
        , invalidEscape "\"\\v\""
        , invalidEscape "\"\\377\""
        , invalidEscape "\"\\77\""
        , invalidEscape "\"\\77a\""
        , Failure
            FailureTest
                { failureInput = "\"\DEL\""
                , failureExpected =
                    unlines
                        [ "<test-string>:1:2:"
                        , "  |"
                        , "1 | \"\DEL\""
                        , "  |  ^"
                        , "unexpected delete"
                        , "expecting '\"' or printable ASCII character"
                        ]
                }
        , Failure
            FailureTest
                { failureInput = "\"\\uD800\""
                , failureExpected =
                    unlines
                        [ "<test-string>:1:8:"
                        , "  |"
                        , "1 | \"\\uD800\""
                        , "  |        ^"
                        , illegalSurrogate "D800"
                        ]
                }
        , Failure
            FailureTest
                { failureInput = "\"\\uZZZZ\""
                , failureExpected =
                    unlines
                        [ "<test-string>:1:4:"
                        , "  |"
                        , "1 | \"\\uZZZZ\""
                        , "  |    ^"
                        , "unexpected 'Z'"
                        , "expecting hexadecimal digit"
                        ]
                }
        , Failure
            FailureTest
                { failureInput = "\"\\UFFFFFFFF\""
                , failureExpected =
                    unlines
                        [ "<test-string>:1:12:"
                        , "  |"
                        , "1 | \"\\UFFFFFFFF\""
                        , "  |            ^"
                        , unrepresentableCode "FFFFFFFF"
                        ]
                }
        , FailureWithoutMessage
            [ ""
            , "'a'"
            , "\"\\z\""
            , "\"\\xzf\""
            , "\"\\u123\""
            , "\"\\U1234567\""
            ]
        ]

invalidEscape :: Text -> ParserTest a
invalidEscape failureInput =
    Failure FailureTest{failureInput, failureExpected}
  where
    failureExpected =
        unlines
            [ "<test-string>:1:4:"
            , "  |"
            , "1 | " ++ unpack failureInput
            , "  |    ^"
            , "expecting escape sequence"
            ]
