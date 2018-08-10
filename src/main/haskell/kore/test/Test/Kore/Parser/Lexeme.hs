module Test.Kore.Parser.Lexeme (test_koreLexeme) where

import Test.Tasty
       ( TestTree, testGroup )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.Parser.Lexeme

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
    parseTree (idParser Object)
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
                "<test-string>:1:1:\n"
                ++ "genericIdRawParser: Invalid first character '['.\n"
            }
        , Failure FailureTest
            { failureInput = "module"
            , failureExpected =
                "<test-string>:1:7:\n"
                ++ "Identifiers should not be keywords: 'module'.\n"
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
        [ success "#a" (testId "#a")
        , success "#`a" (testId "#`a")
        , success "#abc" (testId "#abc")
        , success "#a'" (testId "#a'")
        , success "#a'2" (testId "#a'2")
        , success "#sort" (testId "#sort")
        , success "#\\and" (testId "#\\and")
        , success "#\\not" (testId "#\\not")
        , success "#\\or" (testId "#\\or")
        , success "#\\implies" (testId "#\\implies")
        , success "#\\iff" (testId "#\\iff")
        , success "#\\forall" (testId "#\\forall")
        , success "#\\exists" (testId "#\\exists")
        , success "#\\ceil" (testId "#\\ceil")
        , success "#\\floor" (testId "#\\floor")
        , success "#\\equals" (testId "#\\equals")
        , success "#\\in" (testId "#\\in")
        , success "#\\top" (testId "#\\top")
        , success "#\\bottom" (testId "#\\bottom")
        , success "#\\something" (testId "#\\something")
        , FailureWithoutMessage
            [   "",   "'",   "'a",   "2",   "2a", "`", "`a"
            ,  "#",  "#'",  "#'a",  "#2",  "#2a"
            , "#`", "#`'", "#`'a", "#`2", "#`2a"
            , "a#", "#`\\something"
            , ",", " a", "a"]
        ]

inCurlyBracesParserTests :: [TestTree]
inCurlyBracesParserTests =
    parseTree (inCurlyBracesParser (idParser Object))
        [ success "{a}" (testId "a")
        , success "{ a } " (testId "a")
        , success "{/**/a/**/}/**/" (testId "a")
        , FailureWithoutMessage
            [ "", "{}", " {a}", "{a,b}", "{a{}}", "a}", "{a"]
        ]

inParenthesesParserTests :: [TestTree]
inParenthesesParserTests =
    parseTree (inParenthesesParser (idParser Object))
        [ success "(a)" (testId "a")
        , success "( a ) " (testId "a")
        , success "(/**/a/**/)/**/" (testId "a")
        , FailureWithoutMessage
            [ "", "()", " (a)", "(a,b)", "(a())", "a)", "(a"]
        ]

inSquareBracketsParserTests :: [TestTree]
inSquareBracketsParserTests =
    parseTree (inSquareBracketsParser (idParser Object))
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
            [ ("abc", inCurlyBracesParser (idParser Object))
            , ("de", inParenthesesParser (idParser Object))
            , ("dd", idParser Object)
            , ("df", inSquareBracketsParser (idParser Object))])
        [ success "abc{a}" (testId "a")
        , success "de(a)" (testId "a")
        , success "df[a]" (testId "a")
        , success "df [ a ] " (testId "a")
        , success "dd a" (testId "a")
        , success "df/**/ [/**/ a/**/ ]/**/ " (testId "a")
        , Failure FailureTest
            { failureInput = "dg(a)"
            , failureExpected =
                "<test-string>:1:2:\n"
                ++ "Keyword Based Parsers - unexpected character.\n"
            }
        , Failure FailureTest
            { failureInput = "dda"
            , failureExpected =
                "<test-string>:1:3:\n"
                ++ "Expecting keyword to end.\n"
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
                "<test-string>:1:4:\n"
                ++ "Unfinished comment.\n"
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
            , failureExpected =
                "<test-string>:1:13:\n"
                ++ "Character code 4294967295 outside of the representable "
                ++ "codes.\n"
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
            , failureExpected =
                "<test-string>:1:13:\n"
                ++ "Character code 4294967295 outside of the representable "
                ++ "codes.\n"
            }
        , Failure FailureTest
            { failureInput = "''"
            , failureExpected =
                "<test-string>:1:3:\n"
                ++ "'' is not a valid character literal.\n"
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
