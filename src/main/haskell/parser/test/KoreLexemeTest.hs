module KoreLexemeTest (koreLexemeTests) where

import           Test.Tasty

import           KoreAST
import           KoreLexeme
import           ParserTestUtils

koreLexemeTests :: TestTree
koreLexemeTests =
    testGroup
        "Lexeme Tests"
        [ testGroup "colonParser" colonParserTests
        , testGroup "commaParser" commaParserTests
        , testGroup "curlyPairParser" curlyPairParserTests
        , testGroup "idParser" idParserTests
        , testGroup "inCurlyBracesParser" inCurlyBracesParserTests
        , testGroup "inParenthesesParser" inParenthesesParserTests
        , testGroup "keywordBasedParsers" keywordBasedParsersTests
        , testGroup "metaIdParser" metaIdParserTests
        , testGroup "mlLexemeParser" mlLexemeParserTests
        , testGroup "moduleNameParser" moduleNameParserTests
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
    parseTree (curlyPairParser (idParser Object) moduleNameParser)
        [ Success "{a,B}" (Id "a", ModuleName "B")
        , Success "{ a , B } " (Id "a", ModuleName "B")
        , Success "{/**/a/**/,/**/B/**/}/**/" (Id "a", ModuleName "B")
        , Success "{/*/**/a,/**/B/**/}/**/" (Id "a", ModuleName "B")
        , FailureWithoutMessage
            [ "", " {a,B}", "{a}", "{B}", "{a,}", "{,B}", "{a{},b}"
            , "{a,B,c}", "(a,B)"]
        ]

idParserTests :: [TestTree]
idParserTests =
    parseTree (idParser Object)
        [ Success "A" (Id "A")
        , Success "a" (Id "a")
        , Success "abc" (Id "abc")
        , Success "a'" (Id "a'")
        , Success "a-" (Id "a-")
        , Success "a'2" (Id "a'2")
        , Success "a " (Id "a")
        , Success "a/**/ " (Id "a")
        , Failure
            { failureInput = "["
            , failureExpected =
                "Failed reading: genericIdRawParser: Invalid first character '['."
            }
        , Failure
            { failureInput = "module"
            , failureExpected =
                "Failed reading: Identifiers should not be keywords: 'module'."
            }
        , FailureWithoutMessage
            [   "",   "'",   "'a",   "2",   "2a", "`", "`a"
            ,  "#",  "#'",  "#'a",  "#2",  "#2a"
            , "#`", "#`'", "#`'a", "#`2", "#`2a"
            , "a#", "#a"
            , ",", " a"]
        ]

metaIdParserTests :: [TestTree]
metaIdParserTests =
    parseTree (idParser Meta)
        [ Success "#a" (Id "#a")
        , Success "#`a" (Id "#`a")
        , Success "#abc" (Id "#abc")
        , Success "#a'" (Id "#a'")
        , Success "#a'2" (Id "#a'2")
        , Failure
            { failureInput = "#module"
            , failureExpected =
                "Failed reading: Identifiers should not be keywords: 'module'."
            }
        , FailureWithoutMessage
            [   "",   "'",   "'a",   "2",   "2a", "`", "`a"
            ,  "#",  "#'",  "#'a",  "#2",  "#2a"
            , "#`", "#`'", "#`'a", "#`2", "#`2a"
            , "a#"
            , ",", " a", "a"]
        ]

inCurlyBracesParserTests :: [TestTree]
inCurlyBracesParserTests =
    parseTree (inCurlyBracesParser (idParser Object))
        [ Success "{a}" (Id "a")
        , Success "{ a } " (Id "a")
        , Success "{/**/a/**/}/**/" (Id "a")
        , FailureWithoutMessage
            [ "", "{}", " {a}", "{a,b}", "{a{}}", "a}", "{a"]
        ]

inParenthesesParserTests :: [TestTree]
inParenthesesParserTests =
    parseTree (inParenthesesParser (idParser Object))
        [ Success "(a)" (Id "a")
        , Success "( a ) " (Id "a")
        , Success "(/**/a/**/)/**/" (Id "a")
        , FailureWithoutMessage
            [ "", "()", " (a)", "(a,b)", "(a())", "a)", "(a"]
        ]

inSquareBracketsParserTests :: [TestTree]
inSquareBracketsParserTests =
    parseTree (inSquareBracketsParser (idParser Object))
        [ Success "[a]" (Id "a")
        , Success "[ a ] " (Id "a")
        , Success "[/**/a/**/]/**/" (Id "a")
        , FailureWithoutMessage
            [ "", "[]", " [a]", "[a,b]", "[a[]]", "a]", "[a"]
        ]

keywordBasedParsersTests :: [TestTree]
keywordBasedParsersTests =
    parseTree
        (keywordBasedParsers
            [ ("abc", inCurlyBracesParser (idParser Object))
            , ("de", inParenthesesParser (idParser Object))
            , ("dd", idParser Object)
            , ("df", inSquareBracketsParser (idParser Object))])
        [ Success "abc{a}" (Id "a")
        , Success "de(a)" (Id "a")
        , Success "df[a]" (Id "a")
        , Success "df [ a ] " (Id "a")
        , Success "dd a" (Id "a")
        , Success "df/**/ [/**/ a/**/ ]/**/ " (Id "a")
        , Failure
            { failureInput = "dg(a)"
            , failureExpected =
                "Failed reading: Keyword Based Parsers - unexpected character."
            }
        , Failure
            { failureInput = "dda"
            , failureExpected =
                "Failed reading: Expecting keyword to end."
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

moduleNameParserTests :: [TestTree]
moduleNameParserTests =
    parseTree moduleNameParser
        [ Success "A" (ModuleName "A")
        , Success "A-" (ModuleName "A-")
        , Success "A2" (ModuleName "A2")
        , Success "a'-2" (ModuleName "a'-2")
        , Success "A " (ModuleName "A")
        , Success "A/**/ " (ModuleName "A")
        , FailureWithoutMessage
            [  "",  "-",  "-A",  "2",  "2A"
            , "#", "#A", " A", ","]
        ]

parenPairParserTests :: [TestTree]
parenPairParserTests =
    parseTree (parenPairParser (idParser Object) moduleNameParser)
        [ Success "(a,B)" (Id "a", ModuleName "B")
        , Success "( a , B ) " (Id "a", ModuleName "B")
        , Success "(/**/a/**/,/**/B/**/)/**/" (Id "a", ModuleName "B")
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
        , Failure
            { failureInput = "/*/"
            , failureExpected = "Failed reading: Unfinished comment."
            }
        , FailureWithoutMessage
            [ "a", "/*", "/**", "/***", "/*hello", "/*//", "*/"
            , "/ /", "/**//", "//\na"]
        ]

stringLiteralParserTests :: [TestTree]
stringLiteralParserTests =
    parseTree stringLiteralParser
        [ Success "\"\"" (StringLiteral "")
        , Success "\"a\"" (StringLiteral "a")
        , Success "\"\\'\"" (StringLiteral "'")
        , Success "\"\\\"\"" (StringLiteral "\"")
        , Success "\"\\?\"" (StringLiteral "?")
        , Success "\"\\a\"" (StringLiteral "\7")
        , Success "\"\\b\"" (StringLiteral "\8")
        , Success "\"\\f\"" (StringLiteral "\12")
        , Success "\"\\n\"" (StringLiteral "\10")
        , Success "\"\\r\"" (StringLiteral "\13")
        , Success "\"\\t\"" (StringLiteral "\9")
        , Success "\"\\v\"" (StringLiteral "\11")
        , Success "\"\\377\"" (StringLiteral "\255")
        , Success "\"\\77\"" (StringLiteral "\63")
        , Success "\"\\77a\"" (StringLiteral ("\63" ++ "a"))
        , Success "\"\\xFF\"" (StringLiteral "\255")
        , Success "\"\\xff\"" (StringLiteral "\255")
        , Success "\"\\xF\"" (StringLiteral "\15")
        , Success "\"\\xFr\"" (StringLiteral ("\15" ++ "r"))
        , Success "\"\\u1ABC\"" (StringLiteral "\6844")
        , Success "\"\\u1ABCa\"" (StringLiteral ("\6844" ++ "a"))
        , Success "\"\\u1abc\"" (StringLiteral "\6844")
        , Success "\"\\U000120FF\"" (StringLiteral "\73983")
        , Success "\"\\U000120FFa\"" (StringLiteral ("\73983" ++ "a"))
        , Success "\"\\U000120ff\"" (StringLiteral "\73983")
        , Failure
            { failureInput = "\"\\UFFFFFFFF\""
            , failureExpected = "Failed reading: Character code 4294967295"
                ++ " outside of the representable codes."
            }
        , FailureWithoutMessage
            [ "", "\"\\z\"", "\"\\xzf\"", "\"\\u123\"", "\"\\U1234567\""
            {-  TODO(virgil): It's not clear whether the strings below should
                fail or not. A C hex sequence can be longer than 2 if it fits
                into the char size being considered. Not sure if octals above
                \377 are allowed or not.
            , "\"\\400\"", "\"\\xfff\""
            -}
            ]
        ]
