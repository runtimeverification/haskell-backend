module Test.Kore.Parser.Lexeme (test_koreLexeme) where

import Test.Tasty
    ( TestTree
    , testGroup
    )

import Kore.Parser.Lexeme
import Kore.Syntax.Definition
import Kore.Syntax.StringLiteral

import Test.Kore
import Test.Kore.Parser

test_koreLexeme :: [TestTree]
test_koreLexeme =
    [ testGroup "colonParser" colonParserTests
    , testGroup "commaParser" commaParserTests
    , testGroup "curlyPairParser" curlyPairParserTests
    , testGroup "idParser" idParserTests
    , testGroup "inCurlyBracesParser" inCurlyBracesParserTests
    , testGroup "inParenthesesParser" inParenthesesParserTests
    , testGroup "inSquareBracketsParser" inSquareBracketsParserTests
    , testGroup "keywordBasedParsers" keywordBasedParsersTests
    , testGroup "mlLexemeParser" mlLexemeParserTests
    , testGroup "moduleNameIdParser" moduleNameIdParserTests
    , testGroup "parenPairParser" parenPairParserTests
    , testGroup "skipWhitespace" skipWhitespaceTests
    , testGroup "stringLiteralParser" stringLiteralParserTests
    ]

colonParserTests :: [TestTree]
colonParserTests =
    parseSkipTree colonParser
        [ Skip [":", ": ", ":/**/"]
        , FailureWithoutMessage ["", " :", " ", ","]
        ]

commaParserTests :: [TestTree]
commaParserTests =
    parseSkipTree commaParser
        [ Skip [",", ", ", ",/**/"]
        , FailureWithoutMessage ["", " ,", " ", ":"]
        ]

curlyPairParserTests :: [TestTree]
curlyPairParserTests =
    parseTree (curlyPairParser idParser moduleNameIdParser)
        [ success "{a,B}" (testId "a", ModuleName "B")
        , success "{ a , B } " (testId "a", ModuleName "B")
        , success "{/**/a/**/,/**/B/**/}/**/" (testId "a", ModuleName "B")
        , success "{/*/**/a,/**/B/**/}/**/" (testId "a", ModuleName "B")
        , FailureWithoutMessage
            [ "", " {a,B}", "{a}", "{B}", "{a,}", "{,B}", "{a{},b}"
            , "{a,B,c}", "(a,B)"]
        ]

idParserTests :: [TestTree]
idParserTests =
    parseTree symbolIdParser
        [ success "A" (testId "A")
        , success "a" (testId "a")
        , success "abc" (testId "abc")
        , success "a'" (testId "a'")
        , success "a-" (testId "a-")
        , success "a'2" (testId "a'2")
        , success "a " (testId "a")
        , success "a/**/ " (testId "a")
        , success "\\something" (testId "\\something")
        , Failure FailureTest
            { failureInput = "["
            , failureExpected =
                "<test-string>:1:1:\n\
                \  |\n\
                \1 | [\n\
                \  | ^\n\
                \genericIdRawParser: Invalid first character '['.\n"
            }
        , Failure FailureTest
            { failureInput = "module"
            , failureExpected =
                "<test-string>:1:7:\n\
                \  |\n\
                \1 | module\n\
                \  |       ^\n\
                \Identifiers should not be keywords: 'module'.\n"
            }
        , FailureWithoutMessage
            [   "",   "'",   "'a",   "2",   "2a", "`", "`a"
            ,  "#",  "#'",  "#'a",  "#2",  "#2a"
            , "#`", "#`'", "#`'a", "#`2", "#`2a"
            , "a#"
            , ",", " a"]
        ]

inCurlyBracesParserTests :: [TestTree]
inCurlyBracesParserTests =
    parseTree (inCurlyBracesParser idParser)
        [ success "{a}" (testId "a")
        , success "{ a } " (testId "a")
        , success "{/**/a/**/}/**/" (testId "a")
        , FailureWithoutMessage
            [ "", "{}", " {a}", "{a,b}", "{a{}}", "a}", "{a"]
        ]

inParenthesesParserTests :: [TestTree]
inParenthesesParserTests =
    parseTree (inParenthesesParser idParser)
        [ success "(a)" (testId "a")
        , success "( a ) " (testId "a")
        , success "(/**/a/**/)/**/" (testId "a")
        , FailureWithoutMessage
            [ "", "()", " (a)", "(a,b)", "(a())", "a)", "(a"]
        ]

inSquareBracketsParserTests :: [TestTree]
inSquareBracketsParserTests =
    parseTree (inSquareBracketsParser idParser)
        [ success "[a]" (testId "a")
        , success "[ a ] " (testId "a")
        , success "[/**/a/**/]/**/" (testId "a")
        , FailureWithoutMessage
            [ "", "[]", " [a]", "[a,b]", "[a[]]", "a]", "[a"]
        ]

keywordBasedParsersTests :: [TestTree]
keywordBasedParsersTests =
    parseTree
        (keywordBasedParsers
            [ ("abc", inCurlyBracesParser idParser)
            , ("de", inParenthesesParser idParser)
            , ("dd", idParser)
            , ("df", inSquareBracketsParser idParser)
            ]
        )
        [ success "abc{a}" (testId "a")
        , success "de(a)" (testId "a")
        , success "df[a]" (testId "a")
        , success "df [ a ] " (testId "a")
        , success "dd a" (testId "a")
        , success "df/**/ [/**/ a/**/ ]/**/ " (testId "a")
        , Failure FailureTest
            { failureInput = "dg(a)"
            , failureExpected =
                "<test-string>:1:2:\n\
                \  |\n\
                \1 | dg(a)\n\
                \  |  ^\n\
                \Keyword Based Parsers - unexpected character.\n"
            }
        , Failure FailureTest
            { failureInput = "dda"
            , failureExpected =
                "<test-string>:1:3:\n\
                \  |\n\
                \1 | dda\n\
                \  |   ^\n\
                \Expecting keyword to end.\n"
            }
        , FailureWithoutMessage
            [ "abc(a)", "abc[a]", "de{a}", "de[a]", "df{a}", "dfa)"
            , "abc", "de", "df"
            , "", " de(a)", "(a)"
            ]
        ]

mlLexemeParserTests :: [TestTree]
mlLexemeParserTests =
    parseSkipTree (mlLexemeParser "hello")
    [ Skip ["hello", "hello ", "hello/**/ "]
    , FailureWithoutMessage ["", "Hello", " hello"]
    ]

moduleNameIdParserTests :: [TestTree]
moduleNameIdParserTests =
    parseTree moduleNameIdParser
        [ success "A" (ModuleName "A")
        , success "A-" (ModuleName "A-")
        , success "A2" (ModuleName "A2")
        , success "a'-2" (ModuleName "a'-2")
        , success "A " (ModuleName "A")
        , success "A/**/ " (ModuleName "A")
        , FailureWithoutMessage
            [  "",  "-",  "-A",  "2",  "2A"
            , "#", "#A", " A", ","]
        ]

parenPairParserTests :: [TestTree]
parenPairParserTests =
    parseTree (parenPairParser idParser moduleNameIdParser)
        [ success "(a,B)" (testId "a", ModuleName "B")
        , success "( a , B ) " (testId "a", ModuleName "B")
        , success "(/**/a/**/,/**/B/**/)/**/" (testId "a", ModuleName "B")
        , FailureWithoutMessage
            [ "", " (a,B)", "(a)", "(B)", "(a,)", "(,B)", "(a(),b)"
            , "(a,B,c)", "{a,B}"]
        ]

skipWhitespaceTests :: [TestTree]
skipWhitespaceTests =
    parseSkipTree skipWhitespace
        [ Skip
            [ "", " ", "\n", "\r", "\t", "/**/", "//\n"
            , "/*\n*/", "/*//*/", "/****/", "/* * / */", "/*/*/"
            , "//hello\n", "//hello"
            , "\t//hello\n /* world\n //*/  //!\n"]
        , Failure FailureTest
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
            [ "a", "/*", "/**", "/***", "/*hello", "/*//", "*/"
            , "/ /", "/**//", "//\na"]
        ]

stringLiteralParserTests :: [TestTree]
stringLiteralParserTests =
    parseTree stringLiteralParser
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
        , Failure FailureTest
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
        , Failure FailureTest
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
        , Failure FailureTest
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
        , Failure FailureTest
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
        , Failure FailureTest
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
        , Failure FailureTest
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
            [ "", "'a'", "\"\\z\"", "\"\\xzf\"", "\"\\u123\"", "\"\\U1234567\""
            ]
        ]

invalidEscape :: String -> ParserTest a
invalidEscape failureInput =
    Failure FailureTest { failureInput, failureExpected }
  where
    failureExpected =
        unlines
            [ "<test-string>:1:4:"
            , "  |"
            , "1 | " ++ failureInput
            , "  |    ^"
            , "expecting escape sequence"
            ]
