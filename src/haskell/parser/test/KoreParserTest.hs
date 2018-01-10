import           Test.Tasty
import           Test.Tasty.HUnit

import           KoreAST
import           KoreParser

import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8 as Char8
import           Data.Either (isLeft)

main :: IO ()
main = defaultMain
    (testGroup
        " Parser Tests"
        [ testGroup "sortParser" sortParserTests
        , testGroup "sortListParser" sortListParserTests
        , testGroup "aliasParser" aliasParserTests
        , testGroup "symbolParser" symbolParserTests
        , testGroup "variableParser" variableParserTests
        , testGroup "variableOrTermPatternParser" variableOrTermPatternParserTests
        , testGroup "andPatternParser" andPatternParserTests
        , testGroup "bottomPatternParser" bottomPatternParserTests
        , testGroup "ceilPatternParser" ceilPatternParserTests
        {-
        , testGroup "equalsPatternParser" equalsPatternParserTests
        , testGroup "existsPatternParser" existsPatternParserTests
        -}
        , testGroup "floorPatternParser" floorPatternParserTests
        , testGroup "iffPatternParser" iffPatternParserTests
        , testGroup "impliesPatternParser" impliesPatternParserTests
        {-
        , testGroup "memPatternParser" memPatternParserTests
        , testGroup "notPatternParser" notPatternParserTests
        -}
        , testGroup "orPatternParser" orPatternParserTests
        , testGroup "topPatternParser" topPatternParserTests
        ]
    )

data Success a = Success { successInput :: String, successExpected :: a }
newtype Failure = Failure [String]

sortParserTests :: [TestTree]
sortParserTests =
    parseTree sortParser
        [ Success "var" (SortVariableSort (SortVariable (Id "var")))
        , Success "sort1{}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts = []
                }
        , Success "sort1{sort2}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [SortVariableSort (SortVariable (Id "sort2"))]
                }
        , Success "sort1{sort2, sort3}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [ SortVariableSort (SortVariable (Id "sort2"))
                    , SortVariableSort (SortVariable (Id "sort3"))
                    ]
                }
        , Success "sort1{sort2{sort3}}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [ ActualSort
                        { actualSortName = Id "sort2"
                        , actualSortSorts =
                            [ SortVariableSort (SortVariable (Id "sort3"))
                            ]
                        }
                    ]
                }
        ]
        (Failure ["var1, var2", "var1{var1 var2}"])

sortListParserTests :: [TestTree]
sortListParserTests =
    parseTree sortListParser
        [ Success "" []
        , Success "var" [SortVariableSort (SortVariable (Id "var"))]
        , Success "var1, var2"
            [ SortVariableSort (SortVariable (Id "var1"))
            , SortVariableSort (SortVariable (Id "var2"))
            ]
        , Success "sort1{sort2}, var"
            [ ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [SortVariableSort (SortVariable (Id "sort2"))]
                }
            , SortVariableSort (SortVariable (Id "var"))
            ]
        ]
        (Failure ["var1 var2"])

aliasParserTests :: [TestTree]
aliasParserTests =
    parseTree aliasParser
        [ Success "c1{}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams = []
                }
        , Success "c1{s1}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams =
                    [SortVariableSort (SortVariable (Id "s1"))]
                }
        , Success "c1{s1,s2{s3}}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams =
                    [ SortVariableSort (SortVariable (Id "s1"))
                    , ActualSort
                        { actualSortName = Id "s2"
                        , actualSortSorts =
                            [ SortVariableSort (SortVariable (Id "s3"))
                            ]
                        }
                    ]
                }
        ]
        (Failure ["alias", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}"])

symbolParserTests :: [TestTree]
symbolParserTests =
    parseTree symbolParser
        [ Success "c1{}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams = []
                }
        , Success "c1{s1}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams =
                    [SortVariableSort (SortVariable (Id "s1"))]
                }
        , Success "c1{s1,s2{s3}}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams =
                    [ SortVariableSort (SortVariable (Id "s1"))
                    , ActualSort
                        { actualSortName = Id "s2"
                        , actualSortSorts =
                            [ SortVariableSort (SortVariable (Id "s3"))
                            ]
                        }
                    ]
                }
        ]
        (Failure ["symbol", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}"])

variableParserTests :: [TestTree]
variableParserTests =
    parseTree variableParser
        [ Success "v:s"
            Variable
                { variableName = Id "v"
                , variableSort = SortVariableSort (SortVariable (Id "s"))
                }
        , Success "v:s1{s2}"
            Variable
                { variableName = Id "v"
                , variableSort =
                    ActualSort
                        { actualSortName=Id "s1"
                        , actualSortSorts=
                            [SortVariableSort (SortVariable (Id "s2"))]
                        }
                }
        ]
        (Failure ["", "var", "v:", ":s"])

variableOrTermPatternParserTests :: [TestTree]
variableOrTermPatternParserTests =
    parseTree patternParser
        [ Success "v:s"
            ( VariablePattern Variable
                { variableName = Id "v"
                , variableSort = SortVariableSort (SortVariable (Id "s"))
                }
            )
        , Success "v:s1{s2}"
            ( VariablePattern Variable
                { variableName = Id "v"
                , variableSort =
                    ActualSort
                        { actualSortName=Id "s1"
                        , actualSortSorts=
                            [SortVariableSort (SortVariable (Id "s2"))]
                        }
                }
            )
        , Success "c{s1,s2}(v1:s1, v2:s2)"
            ApplicationPattern
                { applicationPatternSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "c"
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable (Id "s1"))
                            , SortVariableSort (SortVariable (Id "s2"))
                            ]
                        }
                , applicationPatternPatterns =
                    [ VariablePattern Variable
                        { variableName = Id "v1"
                        , variableSort =
                            SortVariableSort (SortVariable (Id "s1"))
                        }
                    , VariablePattern Variable
                        { variableName = Id "v2"
                        , variableSort =
                            SortVariableSort (SortVariable (Id "s2"))
                        }
                    ]
                }
        , Success "c{}()"
            ApplicationPattern
                { applicationPatternSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "c"
                        , symbolOrAliasParams = []
                        }
                , applicationPatternPatterns = []
                }
        ]
        (Failure ["", "var", "v:", ":s", "c(s)", "c{s}"])

andPatternParserTests :: [TestTree]
andPatternParserTests =
    parseTree patternParser
        [ Success "\\and{s}(\"a\", \"b\")"
            AndPattern
                { andPatternSort = SortVariableSort (SortVariable (Id "s"))
                , andPatternFirst = StringLiteralPattern (StringLiteral "a")
                , andPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
            [ "",
              "\\and{s,s}(\"a\", \"b\")",
              "\\and{}(\"a\", \"b\")",
              "\\and{s}(\"a\")",
              "\\and{s}(\"a\", \"b\", \"c\")",
              "\\and{s}(\"a\" \"b\")"])
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree patternParser
        [ Success "\\bottom{s}()"
            (BottomPattern (SortVariableSort (SortVariable (Id "s"))))
        ]
        (Failure
            [ ""
            , "\\bottom()"
            , "\\bottom{}()"
            , "\\bottom{s, s}()"
            , "\\bottom{s}"])
ceilPatternParserTests :: [TestTree]
ceilPatternParserTests =
    parseTree patternParser
        [ Success "\\ceil{s1, s2}(\"a\")"
            CeilPattern
                { ceilPatternFirstSort =
                    SortVariableSort (SortVariable (Id "s1"))
                , ceilPatternSecondSort =
                    SortVariableSort (SortVariable (Id "s2"))
                , ceilPatternPattern = StringLiteralPattern (StringLiteral "a")
                }
        ]
        (Failure
            [ ""
            , "\\ceil{s1, s2}()"
            , "\\ceil{s1}(\"a\")"
            , "\\ceil{s1, s2, s3}(\"a\")"
            , "\\ceil{s1 s2}(\"a\")"
            ])
{-
equalsPatternParserTests :: [TestTree]
equalsPatternParserTests =
    parseTree patternParser
        [ Success "v:s"
        ]
        (Failure [""])
existsPatternParserTests :: [TestTree]
existsPatternParserTests =
    parseTree patternParser
        [ Success "v:s"
        ]
        (Failure [""])
-}
floorPatternParserTests :: [TestTree]
floorPatternParserTests =
    parseTree patternParser
        [ Success "\\floor{s1, s2}(\"a\")"
            FloorPattern
                { floorPatternFirstSort =
                    SortVariableSort (SortVariable (Id "s1"))
                , floorPatternSecondSort =
                    SortVariableSort (SortVariable (Id "s2"))
                , floorPatternPattern = StringLiteralPattern (StringLiteral "a")
                }
        ]
        (Failure
            [ ""
            , "\\floor{s1, s2}()"
            , "\\floor{s1}(\"a\")"
            , "\\floor{s1, s2, s3}(\"a\")"
            , "\\floor{s1 s2}(\"a\")"
            ])
iffPatternParserTests :: [TestTree]
iffPatternParserTests =
    parseTree patternParser
        [ Success "\\iff{s}(\"a\", \"b\")"
            IffPattern
                { iffPatternSort = SortVariableSort (SortVariable (Id "s"))
                , iffPatternFirst = StringLiteralPattern (StringLiteral "a")
                , iffPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
            [ "",
            "\\iff{s,s}(\"a\", \"b\")",
            "\\iff{}(\"a\", \"b\")",
            "\\iff{s}(\"a\")",
            "\\iff{s}(\"a\", \"b\", \"c\")",
            "\\iff{s}(\"a\" \"b\")"])
impliesPatternParserTests :: [TestTree]
impliesPatternParserTests =
    parseTree patternParser
        [ Success "\\implies{s}(\"a\", \"b\")"
            ImpliesPattern
                { impliesPatternSort = SortVariableSort (SortVariable (Id "s"))
                , impliesPatternFirst = StringLiteralPattern (StringLiteral "a")
                , impliesPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
            [ "",
            "\\implies{s,s}(\"a\", \"b\")",
            "\\implies{}(\"a\", \"b\")",
            "\\implies{s}(\"a\")",
            "\\implies{s}(\"a\", \"b\", \"c\")",
            "\\implies{s}(\"a\" \"b\")"])
{-
memPatternParserTests :: [TestTree]
memPatternParserTests =
    parseTree patternParser
        [ Success "v:s"
        ]
        (Failure [""])
notPatternParserTests :: [TestTree]
notPatternParserTests =
    parseTree patternParser
        [ Success "v:s"
        ]
        (Failure [""])
-}
orPatternParserTests :: [TestTree]
orPatternParserTests =
    parseTree patternParser
        [ Success "\\or{s}(\"a\", \"b\")"
            OrPattern
                { orPatternSort = SortVariableSort (SortVariable (Id "s"))
                , orPatternFirst = StringLiteralPattern (StringLiteral "a")
                , orPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
            [ "",
            "\\or{s,s}(\"a\", \"b\")",
            "\\or{}(\"a\", \"b\")",
            "\\or{s}(\"a\")",
            "\\or{s}(\"a\", \"b\", \"c\")",
            "\\or{s}(\"a\" \"b\")"])

topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree patternParser
        [ Success "\\top{s}()"
            (TopPattern (SortVariableSort (SortVariable (Id "s"))))
        ]
        (Failure ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"])
------------------------------------
-- Generic test utilities
------------------------------------

parseTree
    :: (Show a, Eq a) => Parser.Parser a -> [Success a] -> Failure -> [TestTree]
parseTree parser successTests failureTests =
    parseSuccessTree parser successTests
    ++
    parseFailureTree parser failureTests

parseSuccessTree
    :: (Show a, Eq a) => Parser.Parser a -> [Success a] -> [TestTree]
parseSuccessTree parser =
    map
        (\test ->
            testCase
                ("Parsing '" ++ successInput test ++ "'")
                (parseSuccess (successExpected test) parser (successInput test))
        )

parseFailureTree
    :: (Show a, Eq a) => Parser.Parser a -> Failure -> [TestTree]
parseFailureTree parser (Failure tests) =
    map
        (\input ->
            testCase
                ("Failing to parse '" ++ input ++ "'")
                (parseFailure parser input)
        )
        tests

parseSuccess :: (Show a, Eq a) => a -> Parser.Parser a -> String -> Assertion
parseSuccess expected parser input =
  assertEqual
    "Expecting parse success!"
    (Right expected)
    (Parser.parseOnly (parser <* Parser.endOfInput) (Char8.pack input))

parseFailure :: (Show a, Eq a) => Parser.Parser a -> String -> Assertion
parseFailure parser input =
    assertBool
        "Expecting parse failure!"
        (isLeft
            (Parser.parseOnly
                (parser <* Parser.endOfInput)
                (Char8.pack input)))
