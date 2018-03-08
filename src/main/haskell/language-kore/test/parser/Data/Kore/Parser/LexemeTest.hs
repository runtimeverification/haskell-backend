module Data.Kore.Parser.LexemeTest (koreLexemeTests) where

import           Test.Tasty                       (TestTree, testGroup)

import           Data.Kore.AST
import           Data.Kore.Parser.Lexeme
import           Data.Kore.Parser.ParserTestUtils

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
        , testGroup "inSquareBracketsParser" inSquareBracketsParserTests
        , testGroup "keywordBasedParsers" keywordBasedParsersTests
        , testGroup "metaIdParser" metaIdParserTests
        , testGroup "mlLexemeParser" mlLexemeParserTests
        , testGroup "moduleNameParser" moduleNameParserTests
        , testGroup "parenPairParser" parenPairParserTests
        , testGroup "skipWhitespace" skipWhitespaceTests
        , testGroup "stringLiteralParser" stringLiteralParserTests
        , testGroup "charLiteralParser" charLiteralParserTests
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
        [ success "{a,B}" (Id "a", ModuleName "B")
        , success "{ a , B } " (Id "a", ModuleName "B")
        , success "{/**/a/**/,/**/B/**/}/**/" (Id "a", ModuleName "B")
        , success "{/*/**/a,/**/B/**/}/**/" (Id "a", ModuleName "B")
        , FailureWithoutMessage
            [ "", " {a,B}", "{a}", "{B}", "{a,}", "{,B}", "{a{},b}"
            , "{a,B,c}", "(a,B)"]
        ]

idParserTests :: [TestTree]
idParserTests =
    parseTree (idParser Object)
        [ success "A" (Id "A")
        , success "a" (Id "a")
        , success "abc" (Id "abc")
        , success "a'" (Id "a'")
        , success "a-" (Id "a-")
        , success "a'2" (Id "a'2")
        , success "a " (Id "a")
        , success "a/**/ " (Id "a")
        , Failure FailureTest
            { failureInput = "["
            , failureExpected =
                "Failed reading: genericIdRawParser: " ++
                "Invalid first character '['."
            }
        , Failure FailureTest
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
        [ success "#a" (Id "#a")
        , success "#`a" (Id "#`a")
        , success "#abc" (Id "#abc")
        , success "#a'" (Id "#a'")
        , success "#a'2" (Id "#a'2")
        , success "#sort" (Id "#sort")
        , success "#\\and" (Id "#\\and")
        , success "#\\not" (Id "#\\not")
        , success "#\\or" (Id "#\\or")
        , success "#\\implies" (Id "#\\implies")
        , success "#\\iff" (Id "#\\iff")
        , success "#\\forall" (Id "#\\forall")
        , success "#\\exists" (Id "#\\exists")
        , success "#\\ceil" (Id "#\\ceil")
        , success "#\\floor" (Id "#\\floor")
        , success "#\\equals" (Id "#\\equals")
        , success "#\\in" (Id "#\\in")
        , success "#\\top" (Id "#\\top")
        , success "#\\bottom" (Id "#\\bottom")
        , FailureWithoutMessage
            [   "",   "'",   "'a",   "2",   "2a", "`", "`a"
            ,  "#",  "#'",  "#'a",  "#2",  "#2a"
            , "#`", "#`'", "#`'a", "#`2", "#`2a"
            , "a#", "#\\something"
            , ",", " a", "a"]
        ]

inCurlyBracesParserTests :: [TestTree]
inCurlyBracesParserTests =
    parseTree (inCurlyBracesParser (idParser Object))
        [ success "{a}" (Id "a")
        , success "{ a } " (Id "a")
        , success "{/**/a/**/}/**/" (Id "a")
        , FailureWithoutMessage
            [ "", "{}", " {a}", "{a,b}", "{a{}}", "a}", "{a"]
        ]

inParenthesesParserTests :: [TestTree]
inParenthesesParserTests =
    parseTree (inParenthesesParser (idParser Object))
        [ success "(a)" (Id "a")
        , success "( a ) " (Id "a")
        , success "(/**/a/**/)/**/" (Id "a")
        , FailureWithoutMessage
            [ "", "()", " (a)", "(a,b)", "(a())", "a)", "(a"]
        ]

inSquareBracketsParserTests :: [TestTree]
inSquareBracketsParserTests =
    parseTree (inSquareBracketsParser (idParser Object))
        [ success "[a]" (Id "a")
        , success "[ a ] " (Id "a")
        , success "[/**/a/**/]/**/" (Id "a")
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
        [ success "abc{a}" (Id "a")
        , success "de(a)" (Id "a")
        , success "df[a]" (Id "a")
        , success "df [ a ] " (Id "a")
        , success "dd a" (Id "a")
        , success "df/**/ [/**/ a/**/ ]/**/ " (Id "a")
        , Failure FailureTest
            { failureInput = "dg(a)"
            , failureExpected =
                "Failed reading: Keyword Based Parsers - unexpected character."
            }
        , Failure FailureTest
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
    parseTree (parenPairParser (idParser Object) moduleNameParser)
        [ success "(a,B)" (Id "a", ModuleName "B")
        , success "( a , B ) " (Id "a", ModuleName "B")
        , success "(/**/a/**/,/**/B/**/)/**/" (Id "a", ModuleName "B")
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
            , failureExpected = "Failed reading: Unfinished comment."
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
        , success "\"\\'\"" (StringLiteral "'")
        , success "\"\\\"\"" (StringLiteral "\"")
        , success "\"\\?\"" (StringLiteral "?")
        , success "\"\\a\"" (StringLiteral "\7")
        , success "\"\\b\"" (StringLiteral "\8")
        , success "\"\\f\"" (StringLiteral "\12")
        , success "\"\\n\"" (StringLiteral "\10")
        , success "\"\\r\"" (StringLiteral "\13")
        , success "\"\\t\"" (StringLiteral "\9")
        , success "\"\\v\"" (StringLiteral "\11")
        , success "\"\\377\"" (StringLiteral "\255")
        , success "\"\\77\"" (StringLiteral "\63")
        , success "\"\\77a\"" (StringLiteral ("\63" ++ "a"))
        , success "\"\\xFF\"" (StringLiteral "\255")
        , success "\"\\xff\"" (StringLiteral "\255")
        , success "\"\\xF\"" (StringLiteral "\15")
        , success "\"\\xFr\"" (StringLiteral ("\15" ++ "r"))
        , success "\"\\u1ABC\"" (StringLiteral "\6844")
        , success "\"\\u1ABCa\"" (StringLiteral ("\6844" ++ "a"))
        , success "\"\\u1abc\"" (StringLiteral "\6844")
        , success "\"\\U000120FF\"" (StringLiteral "\73983")
        , success "\"\\U000120FFa\"" (StringLiteral ("\73983" ++ "a"))
        , success "\"\\U000120ff\"" (StringLiteral "\73983")
        , Failure FailureTest
            { failureInput = "\"\\UFFFFFFFF\""
            , failureExpected = "Failed reading: Character code 4294967295"
                ++ " outside of the representable codes."
            }
        , FailureWithoutMessage
            [ "", "'a'", "\"\\z\"", "\"\\xzf\"", "\"\\u123\"", "\"\\U1234567\""
            {-  TODO(virgil): It's not clear whether the strings below should
                fail or not. A C hex sequence can be longer than 2 if it fits
                into the char size being considered. Not sure if octals above
                \377 are allowed or not.
            , "\"\\400\"", "\"\\xfff\""
            -}
            ]
        ]

charLiteralParserTests :: [TestTree]
charLiteralParserTests =
    parseTree charLiteralParser
        [ success "'a'" (CharLiteral 'a')
        , success "'\\''" (CharLiteral '\'')
        , success "'\\\"'" (CharLiteral '\"')
        , success "'\\?'" (CharLiteral '?')
        , success "'\\a'" (CharLiteral '\7')
        , success "'\\b'" (CharLiteral '\8')
        , success "'\\f'" (CharLiteral '\12')
        , success "'\\n'" (CharLiteral '\10')
        , success "'\\r'" (CharLiteral '\13')
        , success "'\\t'" (CharLiteral '\9')
        , success "'\\v'" (CharLiteral '\11')
        , success "'\\377'" (CharLiteral '\255')
        , success "'\\77'" (CharLiteral '\63')
        , success "'\\xFF'" (CharLiteral '\255')
        , success "'\\xff'" (CharLiteral '\255')
        , success "'\\xF'" (CharLiteral '\15')
        , success "'\\u1ABC'" (CharLiteral '\6844')
        , success "'\\u1abc'" (CharLiteral '\6844')
        , success "'\\U000120FF'" (CharLiteral '\73983')
        , success "'\\U000120ff'" (CharLiteral '\73983')
        , Failure FailureTest
            { failureInput = "'\\UFFFFFFFF'"
            , failureExpected = "Failed reading: Character code 4294967295"
                ++ " outside of the representable codes."
            }
        , Failure FailureTest
            { failureInput = "''"
            , failureExpected =
                "Failed reading: '' is not a valid character literal."
            }
        , FailureWithoutMessage
            [ "", "'\\z'", "'\\xzf'", "'\\u123'", "'\\U1234567'"
            , "'\\U000120FFa'", "'\\xFr'", "'\\77a'", "'\\u1ABCa'"
            , "'ab'"
            {-  TODO(virgil): It's not clear whether the strings below should
                fail or not. A C hex sequence can be longer than 2 if it fits
                into the char size being considered. Not sure if octals above
                \377 are allowed or not.
            , "'\\400'", "'\\xfff'"
            -}
            ]
        ]
