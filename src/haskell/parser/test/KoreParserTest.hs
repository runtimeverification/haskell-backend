module KoreParserTest (koreParserTests) where

import           Test.Tasty

import           KoreAST
import           KoreParserImpl
import           ParserTestUtils

koreParserTests :: TestTree
koreParserTests =
    testGroup
        "Parser Tests"
        [ testGroup "objectSortParser" objectSortParserTests
        , testGroup "metaSortParser" metaSortParserTests
        , testGroup "objectSortListParser" objectSortListParserTests
        , testGroup "metaSortListParser" metaSortListParserTests
        , testGroup "objectSortVariableParser" objectSortVariableParserTests
        , testGroup "metaSortVariableParser" metaSortVariableParserTests
        , testGroup "sortVariableParser" sortVariableParserTests
        , testGroup "objectAliasParser" objectAliasParserTests
        , testGroup "objectSymbolParser" objectSymbolParserTests
        , testGroup "metaAliasParser" metaAliasParserTests
        , testGroup "metaSymbolParser" metaSymbolParserTests
        , testGroup "variableParser" variableParserTests
        , testGroup "andPatternParser" andPatternParserTests
        , testGroup "applicationPatternParser" applicationPatternParserTests
        , testGroup "bottomPatternParser" bottomPatternParserTests
        , testGroup "ceilPatternParser" ceilPatternParserTests
        , testGroup "equalsPatternParser" equalsPatternParserTests
        , testGroup "existsPatternParser" existsPatternParserTests
        , testGroup "floorPatternParser" floorPatternParserTests
        , testGroup "forallPatternParser" forallPatternParserTests
        , testGroup "iffPatternParser" iffPatternParserTests
        , testGroup "impliesPatternParser" impliesPatternParserTests
        , testGroup "memPatternParser" memPatternParserTests
        , testGroup "notPatternParser" notPatternParserTests
        , testGroup "orPatternParser" orPatternParserTests
        , testGroup "stringLiteralPatternParser" stringLiteralPatternParserTests
        , testGroup "topPatternParser" topPatternParserTests
        , testGroup "variablePatternParser" variablePatternParserTests
        , testGroup "aliasSentenceParser" aliasSentenceParserTests
        , testGroup "axiomSentenceParser" axiomSentenceParserTests
        , testGroup "sortSentenceParser" sortSentenceParserTests
        , testGroup "symbolSentenceParser" symbolSentenceParserTests
        , testGroup "attributesParser" attributesParserTests
        , testGroup "moduleParser" moduleParserTests
        , testGroup "definitionParser" definitionParserTests
        ]

objectSortParserTests :: [TestTree]
objectSortParserTests =
    parseTree (sortParser Object)
        [ Success "var"
            SortVariableSort
                { sortVariableSortType = Object
                , getSortVariableSort = SortVariable Object (Id Object "var")
                }
        , Success "sort1{}"
            ActualSort
                { actualSortType = Object
                , actualSortName = Id Object "sort1"
                , actualSortSorts = []
                }
        , Success "sort1{sort2}"
            ActualSort
                { actualSortType = Object
                , actualSortName = Id Object "sort1"
                , actualSortSorts =
                    [ SortVariableSort
                        { sortVariableSortType = Object
                        , getSortVariableSort =
                            SortVariable Object (Id Object "sort2")
                        }
                    ]
                }
        , Success "sort1{sort2, sort3}"
            ActualSort
                { actualSortType = Object
                , actualSortName = Id Object "sort1"
                , actualSortSorts =
                    [ SortVariableSort
                        { sortVariableSortType = Object
                        , getSortVariableSort =
                            SortVariable Object (Id Object "sort2")
                        }
                    , SortVariableSort
                        { sortVariableSortType = Object
                        , getSortVariableSort =
                            SortVariable Object (Id Object "sort3")
                        }
                    ]
                }
        , Success "sort1{sort2{sort3}}"
            ActualSort
                { actualSortType = Object
                , actualSortName = Id Object "sort1"
                , actualSortSorts =
                    [ ActualSort
                        { actualSortType = Object
                        , actualSortName = Id Object "sort2"
                        , actualSortSorts =
                            [ SortVariableSort Object
                                (SortVariable Object (Id Object "sort3"))
                            ]
                        }
                    ]
                }
        , FailureWithoutMessage ["var1, var2", "var1{var1 var2}"]
        ]

metaSortParserTests :: [TestTree]
metaSortParserTests =
    parseTree (sortParser Meta)
        [ Success "#var"
            (SortVariableSort Meta (SortVariable Meta (Id Meta "#var")))
        , Success "#Char{}" (metaSort CharSort)
        , Success "#CharList{}" (metaSort CharListSort)
        , Success "#Pattern{}" (metaSort PatternSort)
        , Success "#PatternList{}" (metaSort PatternListSort)
        , Success "#Sort{}" (metaSort SortSort)
        , Success "#SortList{}" (metaSort SortListSort)
        , Success "#String{}" (metaSort StringSort)
        , Success "#Symbol{}" (metaSort SymbolSort)
        , Success "#SymbolList{}" (metaSort SymbolListSort)
        , Success "#Variable{}" (metaSort VariableSort)
        , Success "#VariableList{}" (metaSort VariableListSort)
        , Failure
            { failureInput = "#Chart{}"
            , failureExpected =
                "Failed reading: metaSortParser: Invalid constructor: '#Chart'."
            }
        , FailureWithoutMessage
            [ "var1, var2", "var1{var1 var2}"
            , "sort1{sort2, sort3}", "sort1{sort2{sort3}}"
            , "#Char{#Char}"
            ]
        ]

objectSortListParserTests :: [TestTree]
objectSortListParserTests =
    parseTree (sortListParser Object)
        [ Success "" []
        , Success "var"
            [ objectSortVariableSort "var" ]
        , Success "var1, var2"
            [ objectSortVariableSort "var1"
            , objectSortVariableSort "var2"
            ]
        , Success "sort1{sort2}, var"
            [ ActualSort
                { actualSortType = Object
                , actualSortName = Id Object "sort1"
                , actualSortSorts =
                    [ objectSortVariableSort "sort2" ]
                }
            , objectSortVariableSort "var"
            ]
        , FailureWithoutMessage ["var1 var2"]
        ]

metaSortListParserTests :: [TestTree]
metaSortListParserTests =
    parseTree (sortListParser Meta)
        [ Success "" []
        , Success "#var"
            [SortVariableSort Meta (SortVariable Meta (Id Meta "#var"))]
        , Success "#var1, #var2"
            [ SortVariableSort Meta (SortVariable Meta (Id Meta "#var1"))
            , SortVariableSort Meta (SortVariable Meta (Id Meta "#var2"))
            ]
        , Success "#Char{  }  , #var"
            [ metaSort CharSort
            , SortVariableSort Meta (SortVariable Meta (Id Meta "#var"))
            ]
        , FailureWithoutMessage
            [ "#var1 #var2", "#var1, var2" ]
        ]

objectSortVariableParserTests :: [TestTree]
objectSortVariableParserTests =
    parseTree (sortVariableParser Object)
        [ Success "var" (SortVariable Object (Id Object "var"))
        , FailureWithoutMessage ["", "#", "#var"]
        ]

metaSortVariableParserTests :: [TestTree]
metaSortVariableParserTests =
    parseTree (sortVariableParser Meta)
        [ Success "#var" (SortVariable Meta (Id Meta "#var"))
        , FailureWithoutMessage ["", "#", "var"]
        ]

sortVariableParserTests :: [TestTree]
sortVariableParserTests =
    parseTree unifiedSortVariableParser
        [ Success "var"
            ( ObjectSortVariable
                (SortVariable Object (Id Object "var"))
            )
        , Success "#var"
            ( MetaSortVariable
                (SortVariable Meta (Id Meta "#var"))
            )
        , FailureWithoutMessage ["", "#"]
        ]

objectAliasParserTests :: [TestTree]
objectAliasParserTests =
    parseTree (aliasParser Object)
        [ Success "c1{}"
            Alias
                { aliasType = Object
                , aliasConstructor = Id Object "c1"
                , aliasParams = []
                }
        , Success "c1{s1}"
            Alias
                { aliasType = Object
                , aliasConstructor = Id Object "c1"
                , aliasParams = [ objectSortVariableSort "s1" ]
                }
        , Success "c1{s1,s2{s3}}"
            Alias
                { aliasType = Object
                , aliasConstructor = Id Object "c1"
                , aliasParams =
                    [ objectSortVariableSort "s1"
                    , ActualSort
                        { actualSortType = Object
                        , actualSortName = Id Object "s2"
                        , actualSortSorts = [ objectSortVariableSort "s3" ]
                        }
                    ]
                }
        , FailureWithoutMessage
            ["alias", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}"]
        ]

objectSymbolParserTests :: [TestTree]
objectSymbolParserTests =
    parseTree (symbolParser Object)
        [ Success "c1{}"
            Symbol
                { symbolType = Object
                , symbolConstructor = Id Object "c1"
                , symbolParams = []
                }
        , Success "c1{s1}"
            Symbol
                { symbolType = Object
                , symbolConstructor = Id Object "c1"
                , symbolParams = [ objectSortVariableSort "s1" ]
                }
        , Success "c1{s1,s2{s3}}"
            Symbol
                { symbolType = Object
                , symbolConstructor = Id Object "c1"
                , symbolParams =
                    [ objectSortVariableSort "s1"
                    , ActualSort
                        { actualSortType = Object
                        , actualSortName = Id Object "s2"
                        , actualSortSorts = [ objectSortVariableSort "s3" ]
                        }
                    ]
                }
        , FailureWithoutMessage
            ["symbol", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}"]
        ]

metaAliasParserTests :: [TestTree]
metaAliasParserTests =
    parseTree (aliasParser Meta)
        [ Success "#c1{}"
            Alias
                { aliasType = Meta
                , aliasConstructor = Id Meta "#c1"
                , aliasParams = []
                }
        , Success "#c1{#s1}"
            Alias
                { aliasType = Meta
                , aliasConstructor = Id Meta "#c1"
                , aliasParams =
                    [SortVariableSort Meta (SortVariable Meta (Id Meta "#s1"))]
                }
        , Success "#c1{#s1,#Char{}}"
            Alias
                { aliasType = Meta
                , aliasConstructor = Id Meta "#c1"
                , aliasParams =
                    [ SortVariableSort Meta (SortVariable Meta (Id Meta "#s1"))
                    , metaSort CharSort
                    ]
                }
        , FailureWithoutMessage
            ["#alias", "#a1{#a2},#a1{#a2}", "#a1{#a2 #a2}", "#a1{#a2}#a1{#a2}"]
        ]

metaSymbolParserTests :: [TestTree]
metaSymbolParserTests =
    parseTree (symbolParser Meta)
        [ Success "#c1{}"
            Symbol
                { symbolType = Meta
                , symbolConstructor = Id Meta "#c1"
                , symbolParams = []
                }
        , Success "#c1{#s1}"
            Symbol
                { symbolType = Meta
                , symbolConstructor = Id Meta "#c1"
                , symbolParams =
                    [SortVariableSort Meta (SortVariable Meta (Id Meta "#s1"))]
                }
        , Success "#c1{#s1,#CharList{}}"
            Symbol
                { symbolType = Meta
                , symbolConstructor = Id Meta "#c1"
                , symbolParams =
                    [ SortVariableSort Meta (SortVariable Meta (Id Meta "#s1"))
                    , metaSort CharListSort
                    ]
                }
        , FailureWithoutMessage
            ["#symbol", "#a1{#a2},#a1{#a2}", "#a1{#a2 #a2}", "#a1{#a2}#a1{#a2}"]
        ]

variableParserTests :: [TestTree]
variableParserTests =
    parseTree (variableParser Object)
        [ Success "v:s"
            Variable
                { variableType = Object
                , variableName = Id Object "v"
                , variableSort = objectSortVariableSort "s"
                }
        , Success "v:s1{s2}"
            Variable
                { variableType = Object
                , variableName = Id Object "v"
                , variableSort =
                    ActualSort
                        { actualSortType = Object
                        , actualSortName = Id Object "s1"
                        , actualSortSorts = [ objectSortVariableSort "s2" ]
                        }
                }
        , FailureWithoutMessage ["", "var", "v:", ":s"]
        ]

andPatternParserTests :: [TestTree]
andPatternParserTests =
    parseTree patternParser
        [ Success "\\and{s}(\"a\", \"b\")"
            ( ObjectPattern AndPattern
                { andPatternSort = objectSortVariableSort "s"
                , andPatternFirst =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , andPatternSecond =
                    MetaPattern $ StringLiteralPattern (StringLiteral "b")
                }
            )
        , FailureWithoutMessage
            [ ""
            , "\\and{s,s}(\"a\", \"b\")"
            , "\\and{}(\"a\", \"b\")"
            , "\\and{s}(\"a\")"
            , "\\and{s}(\"a\", \"b\", \"c\")"
            , "\\and{s}(\"a\" \"b\")"
            ]
        ]
applicationPatternParserTests :: [TestTree]
applicationPatternParserTests =
    parseTree patternParser
        [ Success "v:s"
            ( ObjectPattern $ VariablePattern Variable
                { variableType = Object
                , variableName = Id Object "v"
                , variableSort = objectSortVariableSort "s"
                }
            )
        , Success "v:s1{s2}"
            ( ObjectPattern $ VariablePattern Variable
                { variableType = Object
                , variableName = Id Object "v"
                , variableSort =
                    ActualSort
                        { actualSortType = Object
                        , actualSortName = Id Object "s1"
                        , actualSortSorts = [ objectSortVariableSort "s2" ]
                        }
                }
            )
        , Success "c{s1,s2}(v1:s1, v2:s2)"
            ( ObjectPattern ApplicationPattern
                { applicationPatternSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasType = Object
                        , symbolOrAliasConstructor = Id Object "c"
                        , symbolOrAliasParams =
                            [ objectSortVariableSort "s1"
                            , objectSortVariableSort "s2" ]
                        }
                , applicationPatternPatterns =
                    [ ObjectPattern $ VariablePattern Variable
                        { variableType = Object
                        , variableName = Id Object "v1"
                        , variableSort = objectSortVariableSort "s1"
                        }
                    , ObjectPattern $ VariablePattern Variable
                        { variableType = Object
                        , variableName = Id Object "v2"
                        , variableSort = objectSortVariableSort "s2"
                        }
                    ]
                }
            )
        , Success "c{}()"
            ( ObjectPattern ApplicationPattern
                { applicationPatternSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasType = Object
                        , symbolOrAliasConstructor = Id Object "c"
                        , symbolOrAliasParams = []
                        }
                , applicationPatternPatterns = []
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree patternParser
        [ Success "\\bottom{s}()"
            (ObjectPattern $ BottomPattern (objectSortVariableSort "s"))
        , FailureWithoutMessage
            [ ""
            , "\\bottom()"
            , "\\bottom{}()"
            , "\\bottom{s, s}()"
            , "\\bottom{s}"
            ]
        ]
ceilPatternParserTests :: [TestTree]
ceilPatternParserTests =
    parseTree patternParser
        [ Success "\\ceil{s1, s2}(\"a\")"
            (ObjectPattern
                CeilPattern
                    { ceilPatternFirstSort = objectSortVariableSort "s1"
                    , ceilPatternSecondSort = objectSortVariableSort "s2"
                    , ceilPatternPattern =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\ceil{s1, s2}()"
            , "\\ceil{s1}(\"a\")"
            , "\\ceil{s1, s2, s3}(\"a\")"
            , "\\ceil{s1 s2}(\"a\")"
            ]
        ]
equalsPatternParserTests :: [TestTree]
equalsPatternParserTests =
    parseTree patternParser
        [ Success "\\equals{s1, s2}(\"a\", \"b\")"
            ( ObjectPattern
                EqualsPattern
                    { equalsPatternFirstSort = objectSortVariableSort "s1"
                    , equalsPatternSecondSort = objectSortVariableSort "s2"
                    , equalsPatternFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , equalsPatternSecond =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\equals{s}(\"a\", \"b\")"
            , "\\equals{s,s,s}(\"a\", \"b\")"
            , "\\equals{s,s}(\"a\")"
            , "\\equals{s,s}(\"a\", \"b\", \"c\")"
            , "\\equals{s,s}(\"a\" \"b\")"
            ]
        ]
existsPatternParserTests :: [TestTree]
existsPatternParserTests =
    parseTree patternParser
        [ Success "\\exists{s}(v:s1, \"b\")"
            (ObjectPattern
                ExistsPattern
                    { existsPatternSort = objectSortVariableSort "s"
                    , existsPatternVariable = ObjectVariable
                        Variable
                            { variableType = Object
                            , variableName = Id Object "v"
                            , variableSort = objectSortVariableSort "s1"
                            }
                    , existsPatternPattern =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\exists{}(v:s1, \"b\")"
            , "\\exists{s,s}(v:s1, \"b\")"
            , "\\exists{s}(\"b\", \"b\")"
            , "\\exists{s}(, \"b\")"
            , "\\exists{s}(\"b\")"
            , "\\exists{s}(v:s1, )"
            , "\\exists{s}(v:s1)"
            , "\\exists{s}()"
            , "\\exists{s}"
            , "\\exists"
            , "\\exists(v:s1, \"b\")"
            ]
        ]
floorPatternParserTests :: [TestTree]
floorPatternParserTests =
    parseTree patternParser
        [ Success "\\floor{s1, s2}(\"a\")"
            ( ObjectPattern
                FloorPattern
                    { floorPatternFirstSort = objectSortVariableSort "s1"
                    , floorPatternSecondSort = objectSortVariableSort "s2"
                    , floorPatternPattern =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\floor{s1, s2}()"
            , "\\floor{s1}(\"a\")"
            , "\\floor{s1, s2, s3}(\"a\")"
            , "\\floor{s1 s2}(\"a\")"
            ]
        ]
forallPatternParserTests :: [TestTree]
forallPatternParserTests =
    parseTree patternParser
        [ Success "\\forall{s}(v:s1, \"b\")"
            ( ObjectPattern
                ForallPattern
                    { forallPatternSort = objectSortVariableSort "s"
                    , forallPatternVariable = ObjectVariable
                        Variable
                            { variableType = Object
                            , variableName = Id Object "v"
                            , variableSort = objectSortVariableSort "s1"
                            }
                    , forallPatternPattern =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\forall{}(v:s1, \"b\")"
            , "\\forall{s,s}(v:s1, \"b\")"
            , "\\forall{s}(\"b\", \"b\")"
            , "\\forall{s}(, \"b\")"
            , "\\forall{s}(\"b\")"
            , "\\forall{s}(v:s1, )"
            , "\\forall{s}(v:s1)"
            , "\\forall{s}()"
            , "\\forall{s}"
            , "\\forall"
            , "\\forall(v:s1, \"b\")"
            ]
        ]
iffPatternParserTests :: [TestTree]
iffPatternParserTests =
    parseTree patternParser
        [ Success "\\iff{s}(\"a\", \"b\")"
            ( ObjectPattern
                IffPattern
                    { iffPatternSort = objectSortVariableSort "s"
                    , iffPatternFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , iffPatternSecond =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\iff{s,s}(\"a\", \"b\")"
            , "\\iff{}(\"a\", \"b\")"
            , "\\iff{s}(\"a\")"
            , "\\iff{s}(\"a\", \"b\", \"c\")"
            , "\\iff{s}(\"a\" \"b\")"]
        ]
impliesPatternParserTests :: [TestTree]
impliesPatternParserTests =
    parseTree patternParser
        [ Success "\\implies{s}(\"a\", \"b\")"
            ( ObjectPattern
                ImpliesPattern
                    { impliesPatternSort = objectSortVariableSort "s"
                    , impliesPatternFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , impliesPatternSecond =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\implies{s,s}(\"a\", \"b\")"
            , "\\implies{}(\"a\", \"b\")"
            , "\\implies{s}(\"a\")"
            , "\\implies{s}(\"a\", \"b\", \"c\")"
            , "\\implies{s}(\"a\" \"b\")"]
        ]
memPatternParserTests :: [TestTree]
memPatternParserTests =
    parseTree patternParser
        [ Success "\\mem{s1,s2}(v:s3, \"b\")"
            ( ObjectPattern
                MemPattern
                    { memPatternFirstSort = objectSortVariableSort "s1"
                    , memPatternSecondSort = objectSortVariableSort "s2"
                    , memPatternVariable = ObjectVariable
                        Variable
                            { variableType = Object
                            , variableName = Id Object "v"
                            , variableSort = objectSortVariableSort "s3"
                            }
                    , memPatternPattern =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\mem{s}(v:s1, \"b\")"
            , "\\mem{s,s,s}(v:s1, \"b\")"
            , "\\mem{s,s}(\"b\", \"b\")"
            , "\\mem{s,s}(, \"b\")"
            , "\\mem{s,s}(\"b\")"
            , "\\mem{s,s}(v:s1, )"
            , "\\mem{s,s}(v:s1)"
            , "\\mem{s,s}()"
            , "\\mem{s,s}"
            , "\\mem"
            , "\\mem(v:s1, \"b\")"
            ]
        ]
notPatternParserTests :: [TestTree]
notPatternParserTests =
    parseTree patternParser
        [ Success "\\not{s}(\"a\")"
            ( ObjectPattern
                NotPattern
                    { notPatternSort = objectSortVariableSort "s"
                    , notPatternPattern =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\not{s,s}(\"a\")"
            , "\\not{}(\"a\")"
            , "\\not{s}()"
            , "\\not{s}(\"a\", \"b\")"
            , "\\not{s}"
            , "\\not(\"a\")"
            ]
        ]
orPatternParserTests :: [TestTree]
orPatternParserTests =
    parseTree patternParser
        [ Success "\\or{s}(\"a\", \"b\")"
            ( ObjectPattern
                OrPattern
                    { orPatternSort = objectSortVariableSort "s"
                    , orPatternFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , orPatternSecond =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\or{s,s}(\"a\", \"b\")"
            , "\\or{}(\"a\", \"b\")"
            , "\\or{s}(\"a\")"
            , "\\or{s}(\"a\", \"b\", \"c\")"
            , "\\or{s}(\"a\" \"b\")"]
        ]
stringLiteralPatternParserTests :: [TestTree]
stringLiteralPatternParserTests =
    parseTree patternParser
        [ Success "\"hello\""
            (MetaPattern $ StringLiteralPattern (StringLiteral "hello"))
        , Success "\"\""
            (MetaPattern $ StringLiteralPattern (StringLiteral ""))
        , Success "\"\\\"\""
            (MetaPattern $ StringLiteralPattern (StringLiteral "\""))
        , FailureWithoutMessage ["", "\""]
        ]
topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree patternParser
        [ Success "\\top{s}()"
            (ObjectPattern $ TopPattern (objectSortVariableSort "s"))
        , FailureWithoutMessage
            ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"]
        ]
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
    parseTree patternParser
        [ Success "v:s"
            ( ObjectPattern $ VariablePattern Variable
                { variableType = Object
                , variableName = Id Object "v"
                , variableSort = objectSortVariableSort "s"
                }
            )
        , Success "v:s1{s2}"
            ( ObjectPattern $ VariablePattern Variable
                { variableType = Object
                , variableName = Id Object "v"
                , variableSort =
                    ActualSort
                        { actualSortType = Object
                        , actualSortName=Id Object "s1"
                        , actualSortSorts = [ objectSortVariableSort "s2" ]
                        }
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]

aliasSentenceParserTests :: [TestTree]
aliasSentenceParserTests =
    parseTree sentenceParser
        [ Success "alias a{s1}(s2):s3[\"a\"]"
            ( ObjectSymbolOrAliasSentence
                AliasSentence
                    { aliasSentenceAlias = Alias
                        { aliasType = Object
                        , aliasConstructor = Id Object "a"
                        , aliasParams = [ objectSortVariableSort "s1" ]
                        }
                    , aliasSentenceSorts = [ objectSortVariableSort "s2"]
                    , aliasSentenceReturnSort = objectSortVariableSort "s3"
                    , aliasSentenceAttributes =
                        Attributes
                            [MetaPattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
            )
        , Success "alias a { s1 , s2 } ( s3, s4 ) : s5 [ \"a\" , \"b\" ]"
            ( ObjectSymbolOrAliasSentence
                AliasSentence
                    { aliasSentenceAlias = Alias
                        { aliasType = Object
                        , aliasConstructor = Id Object "a"
                        , aliasParams =
                            [ objectSortVariableSort "s1"
                            , objectSortVariableSort "s2"
                            ]
                        }
                    , aliasSentenceSorts =
                        [ objectSortVariableSort "s3"
                        , objectSortVariableSort "s4"
                        ]
                    , aliasSentenceReturnSort = objectSortVariableSort "s5"
                    , aliasSentenceAttributes =
                        Attributes
                            [ MetaPattern $
                                StringLiteralPattern (StringLiteral "a")
                            , MetaPattern $
                                StringLiteralPattern (StringLiteral "b")
                            ]
                    }
            )
        , Success "alias a{}():s3[]"
            ( ObjectSymbolOrAliasSentence
                AliasSentence
                    { aliasSentenceAlias = Alias
                        { aliasType = Object
                        , aliasConstructor = Id Object "a"
                        , aliasParams = []
                        }
                    , aliasSentenceSorts = []
                    , aliasSentenceReturnSort = objectSortVariableSort "s3"
                    , aliasSentenceAttributes = Attributes []
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "a{s1}(s2):s3[\"a\"]"
            , "alias {s1}(s2):s3[\"a\"]"
            , "alias a(s2):s3[\"a\"]"
            , "alias a{s1}:s3[\"a\"]"
            , "alias a{s1}(s2)s3[\"a\"]"
            , "alias a{s1}(s2):[\"a\"]"
            , "alias a{s1}(s2)[\"a\"]"
            , "alias a{s1}(s2):s3"
            ]
        ]

axiomSentenceParserTests :: [TestTree]
axiomSentenceParserTests =
    parseTree sentenceParser
        [ Success "axiom{sv1}\"a\"[\"b\"]"
            AxiomSentence
                { axiomSentenceParameters =
                    [ObjectSortVariable
                        (SortVariable Object (Id Object "sv1"))]
                , axiomSentencePattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "axiom{}\"a\"[\"b\"]"
            AxiomSentence
                { axiomSentenceParameters = []
                , axiomSentencePattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
        , Success "axiom { sv1 , sv2 } \"a\" [ \"b\" ] "
            AxiomSentence
                { axiomSentenceParameters =
                    [ ObjectSortVariable
                        (SortVariable Object (Id Object "sv1"))
                    , ObjectSortVariable
                        (SortVariable Object (Id Object "sv2"))
                    ]
                , axiomSentencePattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
        , FailureWithoutMessage
            [ ""
            , "{sv1}\"a\"[\"b\"]"
            , "axiom\"a\"[\"b\"]"
            -- , "axiom{}\"a\"[\"b\"]" See the TODO above.
            , "axiom{sv1}[\"b\"]"
            , "axiom{sv1}\"a\""
            ]
        ]

sortSentenceParserTests :: [TestTree]
sortSentenceParserTests =
    parseTree sentenceParser
        [ Success "sort { sv1 } s1 [ \"a\" ]"
            SortSentence
                { sortSentenceParameters =
                    [ ObjectSortVariable
                        (SortVariable Object (Id Object "sv1"))
                    ]
                , sortSentenceSort = objectSortVariableSort "s1"
                , sortSentenceAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "sort {} s1 [ \"a\" ]"
            SortSentence
                { sortSentenceParameters = []
                , sortSentenceSort = objectSortVariableSort "s1"
                , sortSentenceAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
        , FailureWithoutMessage
            [ ""
            , "{ sv1 } s1 [ \"a\" ]"
            , "sort s1 [ \"a\" ]"
            , "sort { sv1 } [ \"a\" ]"
            , "sort { sv1 } s1 "
            ]
        ]

symbolSentenceParserTests :: [TestTree]
symbolSentenceParserTests =
    parseTree sentenceParser
        [ Success "symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( ObjectSymbolOrAliasSentence
                SymbolSentence
                    { symbolSentenceSymbol = Symbol
                        { symbolType = Object
                        , symbolConstructor = Id Object "sy1"
                        , symbolParams = [ objectSortVariableSort "s1" ]
                        }
                    , symbolSentenceSorts = [ objectSortVariableSort "s1" ]
                    , symbolSentenceReturnSort = objectSortVariableSort "s1"
                    , symbolSentenceAttributes =
                        Attributes
                            [MetaPattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
            )
        , Success "symbol sy1 {} () : s1 [] "
            ( ObjectSymbolOrAliasSentence
                SymbolSentence
                    { symbolSentenceSymbol = Symbol
                        { symbolType = Object
                        , symbolConstructor = Id Object "sy1"
                        , symbolParams = []
                        }
                    , symbolSentenceSorts = []
                    , symbolSentenceReturnSort = objectSortVariableSort "s1"
                    , symbolSentenceAttributes = Attributes []
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            , "symbol { s1 } ( s1 ) : s1 [\"a\"] "
            , "symbol sy1 ( s1 ) : s1 [\"a\"] "
            , "symbol sy1 { s1 } : s1 [\"a\"] "
            , "symbol sy1 { s1 } ( s1 ) s1 [\"a\"] "
            , "symbol sy1 { s1 } ( s1 ) : [\"a\"] "
            , "symbol sy1 { s1 } ( s1 ) : s1 "
            , "symbol sy1 { s1 } ( s1 ) [\"a\"] "
            ]
        ]

attributesParserTests :: [TestTree]
attributesParserTests =
    parseTree attributesParser
        [ Success "[\"a\"]"
            (Attributes
                [MetaPattern $ StringLiteralPattern (StringLiteral "a")])
        , Success "[]"
            (Attributes [])
        , Success "[\"a\", \"b\"]"
            (Attributes
                [ MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , MetaPattern $ StringLiteralPattern (StringLiteral "b")
                ])
        , FailureWithoutMessage ["", "a", "\"a\"", "[\"a\" \"a\"]"]
        ]


moduleParserTests :: [TestTree]
moduleParserTests =
    parseTree moduleParser
        [ Success "module MN sort{}c[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ SortSentence
                        { sortSentenceParameters = []
                        , sortSentenceSort = objectSortVariableSort "c"
                        , sortSentenceAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
        , Success "module MN sort{}c[] sort{}c[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ SortSentence
                        { sortSentenceParameters = []
                        , sortSentenceSort = objectSortVariableSort "c"
                        , sortSentenceAttributes = Attributes []
                        }
                    , SortSentence
                        { sortSentenceParameters = []
                        , sortSentenceSort = objectSortVariableSort "c"
                        , sortSentenceAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
        , Success "module MN endmodule []"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences = []
                , moduleAttributes = Attributes []
                }
        , FailureWithoutMessage
            [ ""
            , "MN sort{}c[] endmodule [\"a\"]"
            , "module sort{}c[] endmodule [\"a\"]"
            , "module MN sort{}c[] [\"a\"]"
            , "module MN sort{}c[] endmodule"
            ]
        ]

definitionParserTests :: [TestTree]
definitionParserTests =
    parseTree definitionParser
        [ Success "[\"a\"] module M sort{}c[] endmodule [\"b\"]"
            Definition
                { definitionAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                , definitionModules =
                    Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ SortSentence
                                { sortSentenceParameters = []
                                , sortSentenceSort = objectSortVariableSort "c"
                                , sortSentenceAttributes = Attributes []
                                }
                            ]
                        , moduleAttributes =
                            Attributes
                                [MetaPattern $
                                    StringLiteralPattern (StringLiteral "b")]
                        }
                }
        , FailureWithoutMessage
            [ ""
            , "[]"
            , "module M sort{}c[] endmodule [\"b\"]"
            , "[\"a\"] module M sort{}c[] endmodule [\"b\"] "
                ++ "module O sort{}c[] endmodule [\"c\"]"
            ]
        ]

------------------------------------
-- Generic test utilities
------------------------------------

objectSortVariableSort :: String -> Sort Object
objectSortVariableSort name =
    SortVariableSort
        { sortVariableSortType = Object
        , getSortVariableSort =
            SortVariable
                { sortVariableType = Object
                , getSortVariable = Id Object name
                }
        }