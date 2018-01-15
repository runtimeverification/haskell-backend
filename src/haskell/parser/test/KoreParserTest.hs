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
    parseTree objectSortParser
        [ Success "var" (ObjectSortVariableSort (ObjectSortVariable (Id "var")))
        , Success "sort1{}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts = []
                }
        , Success "sort1{sort2}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [ObjectSortVariableSort (ObjectSortVariable (Id "sort2"))]
                }
        , Success "sort1{sort2, sort3}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [ ObjectSortVariableSort (ObjectSortVariable (Id "sort2"))
                    , ObjectSortVariableSort (ObjectSortVariable (Id "sort3"))
                    ]
                }
        , Success "sort1{sort2{sort3}}"
            ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [ ActualSort
                        { actualSortName = Id "sort2"
                        , actualSortSorts =
                            [ ObjectSortVariableSort
                                (ObjectSortVariable (Id "sort3"))
                            ]
                        }
                    ]
                }
        , FailureWithoutMessage ["var1, var2", "var1{var1 var2}"]
        ]

metaSortParserTests :: [TestTree]
metaSortParserTests =
    parseTree metaSortParser
        [ Success "#var"
            (MetaSortVariableMetaSort (MetaSortVariable (MetaId "#var")))
        , Success "#Char{}" CharMetaSort
        , Success "#CharList{}" CharListMetaSort
        , Success "#Pattern{}" PatternMetaSort
        , Success "#PatternList{}" PatternListMetaSort
        , Success "#ObjectSort{}" SortMetaSort
        , Success "#SortList{}" SortListMetaSort
        , Success "#String{}" StringMetaSort
        , Success "#ObjectSymbol{}" SymbolMetaSort
        , Success "#SymbolList{}" SymbolListMetaSort
        , Success "#Variable{}" VariableMetaSort
        , Success "#VariableList{}" VariableListMetaSort
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
    parseTree objectSortListParser
        [ Success "" []
        , Success "var" [ObjectSortVariableSort (ObjectSortVariable (Id "var"))]
        , Success "var1, var2"
            [ ObjectSortVariableSort (ObjectSortVariable (Id "var1"))
            , ObjectSortVariableSort (ObjectSortVariable (Id "var2"))
            ]
        , Success "sort1{sort2}, var"
            [ ActualSort
                { actualSortName = Id "sort1"
                , actualSortSorts =
                    [ObjectSortVariableSort (ObjectSortVariable (Id "sort2"))]
                }
            , ObjectSortVariableSort (ObjectSortVariable (Id "var"))
            ]
        , FailureWithoutMessage ["var1 var2"]
        ]

metaSortListParserTests :: [TestTree]
metaSortListParserTests =
    parseTree metaSortListParser
        [ Success "" []
        , Success "#var"
            [MetaSortVariableMetaSort (MetaSortVariable (MetaId "#var"))]
        , Success "#var1, #var2"
            [ MetaSortVariableMetaSort (MetaSortVariable (MetaId "#var1"))
            , MetaSortVariableMetaSort (MetaSortVariable (MetaId "#var2"))
            ]
        , Success "#Char{  }  , #var"
            [ CharMetaSort
            , MetaSortVariableMetaSort (MetaSortVariable (MetaId "#var"))
            ]
        , FailureWithoutMessage
            [ "#var1 #var2", "#var1, var2" ]
        ]

objectSortVariableParserTests :: [TestTree]
objectSortVariableParserTests =
    parseTree objectSortVariableParser
        [ Success "var" (ObjectSortVariable (Id "var"))
        , FailureWithoutMessage ["", "#", "#var"]
        ]

metaSortVariableParserTests :: [TestTree]
metaSortVariableParserTests =
    parseTree metaSortVariableParser
        [ Success "#var" (MetaSortVariable (MetaId "#var"))
        , FailureWithoutMessage ["", "#", "var"]
        ]

sortVariableParserTests :: [TestTree]
sortVariableParserTests =
    parseTree sortVariableParser
        [ Success "var"
            ( ObjectSortVariableSortVariable
                (ObjectSortVariable (Id "var"))
            )
        , Success "#var"
            ( MetaSortVariableSortVariable
                (MetaSortVariable (MetaId "#var"))
            )
        , FailureWithoutMessage ["", "#"]
        ]

objectAliasParserTests :: [TestTree]
objectAliasParserTests =
    parseTree objectAliasParser
        [ Success "c1{}"
            ObjectAlias
                { objectAliasConstructor = Id "c1"
                , objectAliasParams = []
                }
        , Success "c1{s1}"
            ObjectAlias
                { objectAliasConstructor = Id "c1"
                , objectAliasParams =
                    [ObjectSortVariableSort (ObjectSortVariable (Id "s1"))]
                }
        , Success "c1{s1,s2{s3}}"
            ObjectAlias
                { objectAliasConstructor = Id "c1"
                , objectAliasParams =
                    [ ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                    , ActualSort
                        { actualSortName = Id "s2"
                        , actualSortSorts =
                            [ ObjectSortVariableSort (ObjectSortVariable (Id "s3"))
                            ]
                        }
                    ]
                }
        , FailureWithoutMessage ["alias", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}"]
        ]

objectSymbolParserTests :: [TestTree]
objectSymbolParserTests =
    parseTree objectSymbolParser
        [ Success "c1{}"
            ObjectSymbol
                { objectSymbolConstructor = Id "c1"
                , objectSymbolParams = []
                }
        , Success "c1{s1}"
            ObjectSymbol
                { objectSymbolConstructor = Id "c1"
                , objectSymbolParams =
                    [ObjectSortVariableSort (ObjectSortVariable (Id "s1"))]
                }
        , Success "c1{s1,s2{s3}}"
            ObjectSymbol
                { objectSymbolConstructor = Id "c1"
                , objectSymbolParams =
                    [ ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                    , ActualSort
                        { actualSortName = Id "s2"
                        , actualSortSorts =
                            [ ObjectSortVariableSort (ObjectSortVariable (Id "s3"))
                            ]
                        }
                    ]
                }
        , FailureWithoutMessage ["symbol", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}"]
        ]

metaAliasParserTests :: [TestTree]
metaAliasParserTests =
    parseTree metaAliasParser
        [ Success "#c1{}"
            MetaAlias
                { metaAliasConstructor = MetaId "#c1"
                , metaAliasParams = []
                }
        , Success "#c1{#s1}"
            MetaAlias
                { metaAliasConstructor = MetaId "#c1"
                , metaAliasParams =
                    [MetaSortVariableMetaSort (MetaSortVariable (MetaId "#s1"))]
                }
        , Success "#c1{#s1,#Char{}}"
            MetaAlias
                { metaAliasConstructor = MetaId "#c1"
                , metaAliasParams =
                    [ MetaSortVariableMetaSort (MetaSortVariable (MetaId "#s1"))
                    , CharMetaSort
                    ]
                }
        , FailureWithoutMessage ["#alias", "#a1{#a2},#a1{#a2}", "#a1{#a2 #a2}", "#a1{#a2}#a1{#a2}"]
        ]

metaSymbolParserTests :: [TestTree]
metaSymbolParserTests =
    parseTree metaSymbolParser
        [ Success "#c1{}"
            MetaSymbol
                { metaSymbolConstructor = MetaId "#c1"
                , metaSymbolParams = []
                }
        , Success "#c1{#s1}"
            MetaSymbol
                { metaSymbolConstructor = MetaId "#c1"
                , metaSymbolParams =
                    [MetaSortVariableMetaSort (MetaSortVariable (MetaId "#s1"))]
                }
        , Success "#c1{#s1,#CharList{}}"
            MetaSymbol
                { metaSymbolConstructor = MetaId "#c1"
                , metaSymbolParams =
                    [ MetaSortVariableMetaSort (MetaSortVariable (MetaId "#s1"))
                    , CharListMetaSort
                    ]
                }
        , FailureWithoutMessage ["#symbol", "#a1{#a2},#a1{#a2}", "#a1{#a2 #a2}", "#a1{#a2}#a1{#a2}"]
        ]

variableParserTests :: [TestTree]
variableParserTests =
    parseTree variableParser
        [ Success "v:s"
            Variable
                { variableName = Id "v"
                , variableSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                }
        , Success "v:s1{s2}"
            Variable
                { variableName = Id "v"
                , variableSort =
                    ActualSort
                        { actualSortName=Id "s1"
                        , actualSortSorts=
                            [ObjectSortVariableSort (ObjectSortVariable (Id "s2"))]
                        }
                }
        , FailureWithoutMessage ["", "var", "v:", ":s"]
        ]

andPatternParserTests :: [TestTree]
andPatternParserTests =
    parseTree patternParser
        [ Success "\\and{s}(\"a\", \"b\")"
            AndPattern
                { andPatternSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , andPatternFirst = StringLiteralPattern (StringLiteral "a")
                , andPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
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
            ( VariablePattern Variable
                { variableName = Id "v"
                , variableSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                }
            )
        , Success "v:s1{s2}"
            ( VariablePattern Variable
                { variableName = Id "v"
                , variableSort =
                    ActualSort
                        { actualSortName=Id "s1"
                        , actualSortSorts=
                            [ObjectSortVariableSort (ObjectSortVariable (Id "s2"))]
                        }
                }
            )
        , Success "c{s1,s2}(v1:s1, v2:s2)"
            ApplicationPattern
                { applicationPatternSymbolOrAlias =
                    ObjectSymbolOrAlias
                        { objectSymbolOrAliasConstructor = Id "c"
                        , objectSymbolOrAliasParams =
                            [ ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                            , ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                            ]
                        }
                , applicationPatternPatterns =
                    [ VariablePattern Variable
                        { variableName = Id "v1"
                        , variableSort =
                            ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                        }
                    , VariablePattern Variable
                        { variableName = Id "v2"
                        , variableSort =
                            ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                        }
                    ]
                }
        , Success "c{}()"
            ApplicationPattern
                { applicationPatternSymbolOrAlias =
                    ObjectSymbolOrAlias
                        { objectSymbolOrAliasConstructor = Id "c"
                        , objectSymbolOrAliasParams = []
                        }
                , applicationPatternPatterns = []
                }
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree patternParser
        [ Success "\\bottom{s}()"
            (BottomPattern (ObjectSortVariableSort (ObjectSortVariable (Id "s"))))
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
            CeilPattern
                { ceilPatternFirstSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , ceilPatternSecondSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                , ceilPatternPattern = StringLiteralPattern (StringLiteral "a")
                }
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
            EqualsPattern
                { equalsPatternFirstSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , equalsPatternSecondSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                , equalsPatternFirst = StringLiteralPattern (StringLiteral "a")
                , equalsPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
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
            ExistsPattern
                { existsPatternSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , existsPatternVariable = Variable
                    { variableName = Id "v"
                    , variableSort = ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                    }
                , existsPatternPattern =
                    StringLiteralPattern (StringLiteral "b")
                }
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
            FloorPattern
                { floorPatternFirstSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , floorPatternSecondSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                , floorPatternPattern = StringLiteralPattern (StringLiteral "a")
                }
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
            ForallPattern
                { forallPatternSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , forallPatternVariable = Variable
                    { variableName = Id "v"
                    , variableSort = ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                    }
                , forallPatternPattern =
                    StringLiteralPattern (StringLiteral "b")
                }
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
            IffPattern
                { iffPatternSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , iffPatternFirst = StringLiteralPattern (StringLiteral "a")
                , iffPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
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
            ImpliesPattern
                { impliesPatternSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , impliesPatternFirst = StringLiteralPattern (StringLiteral "a")
                , impliesPatternSecond =
                    StringLiteralPattern (StringLiteral "b")
                }
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
            MemPattern
                { memPatternFirstSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , memPatternSecondSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                , memPatternVariable = Variable
                    { variableName = Id "v"
                    , variableSort = ObjectSortVariableSort (ObjectSortVariable (Id "s3"))
                    }
                , memPatternPattern =
                    StringLiteralPattern (StringLiteral "b")
                }
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
            NotPattern
                { notPatternSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , notPatternPattern = StringLiteralPattern (StringLiteral "a")
                }
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
            OrPattern
                { orPatternSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                , orPatternFirst = StringLiteralPattern (StringLiteral "a")
                , orPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
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
        [ Success "\"hello\"" (StringLiteralPattern (StringLiteral "hello"))
        , Success "\"\"" (StringLiteralPattern (StringLiteral ""))
        , Success "\"\\\"\"" (StringLiteralPattern (StringLiteral "\""))
        , FailureWithoutMessage ["", "\""]
        ]
topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree patternParser
        [ Success "\\top{s}()"
            (TopPattern (ObjectSortVariableSort (ObjectSortVariable (Id "s"))))
        , FailureWithoutMessage ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"]
        ]
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
    parseTree patternParser
        [ Success "v:s"
            ( VariablePattern Variable
                { variableName = Id "v"
                , variableSort = ObjectSortVariableSort (ObjectSortVariable (Id "s"))
                }
            )
        , Success "v:s1{s2}"
            ( VariablePattern Variable
                { variableName = Id "v"
                , variableSort =
                    ActualSort
                        { actualSortName=Id "s1"
                        , actualSortSorts=
                            [ObjectSortVariableSort (ObjectSortVariable (Id "s2"))]
                        }
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]

aliasSentenceParserTests :: [TestTree]
aliasSentenceParserTests =
    parseTree sentenceParser
        [ Success "alias a{s1}(s2):s3[\"a\"]"
            AliasSentence
                { aliasSentenceAlias = ObjectAlias
                    { objectAliasConstructor = Id "a"
                    , objectAliasParams = [ObjectSortVariableSort (ObjectSortVariable (Id "s1"))]
                    }
                , aliasSentenceSorts =
                    [ObjectSortVariableSort (ObjectSortVariable (Id "s2"))]
                , aliasSentenceReturnSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s3"))
                , aliasSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        , Success "alias a { s1 , s2 } ( s3, s4 ) : s5 [ \"a\" , \"b\" ]"
            AliasSentence
                { aliasSentenceAlias = ObjectAlias
                    { objectAliasConstructor = Id "a"
                    , objectAliasParams =
                        [ ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                        , ObjectSortVariableSort (ObjectSortVariable (Id "s2"))
                        ]
                    }
                , aliasSentenceSorts =
                    [ ObjectSortVariableSort (ObjectSortVariable (Id "s3"))
                    , ObjectSortVariableSort (ObjectSortVariable (Id "s4"))
                    ]
                , aliasSentenceReturnSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s5"))
                , aliasSentenceAttributes =
                    Attributes
                        [ StringLiteralPattern (StringLiteral "a")
                        , StringLiteralPattern (StringLiteral "b")
                        ]
                }
        , Success "alias a{}():s3[]"
            AliasSentence
                { aliasSentenceAlias = ObjectAlias
                    { objectAliasConstructor = Id "a"
                    , objectAliasParams = []
                    }
                , aliasSentenceSorts = []
                , aliasSentenceReturnSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s3"))
                , aliasSentenceAttributes = Attributes []
                }
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
                    [ObjectSortVariableSortVariable
                        (ObjectSortVariable (Id "sv1"))]
                , axiomSentencePattern =
                    StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes [StringLiteralPattern (StringLiteral "b")]
                }
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "axiom{}\"a\"[\"b\"]"
            AxiomSentence
                { axiomSentenceParameters = []
                , axiomSentencePattern =
                    StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes [StringLiteralPattern (StringLiteral "b")]
                }
        , Success "axiom { sv1 , sv2 } \"a\" [ \"b\" ] "
            AxiomSentence
                { axiomSentenceParameters =
                    [ ObjectSortVariableSortVariable
                        (ObjectSortVariable (Id "sv1"))
                    , ObjectSortVariableSortVariable
                        (ObjectSortVariable (Id "sv2"))
                    ]
                , axiomSentencePattern =
                    StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes [StringLiteralPattern (StringLiteral "b")]
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
                    [ ObjectSortVariableSortVariable
                        (ObjectSortVariable (Id "sv1"))
                    ]
                , sortSentenceSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , sortSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "sort {} s1 [ \"a\" ]"
            SortSentence
                { sortSentenceParameters = []
                , sortSentenceSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , sortSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
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
            SymbolSentence
                { symbolSentenceSymbol = ObjectSymbol
                    { objectSymbolConstructor = Id "sy1"
                    , objectSymbolParams =
                        [ObjectSortVariableSort (ObjectSortVariable (Id "s1"))]
                    }
                , symbolSentenceSorts =
                    [ObjectSortVariableSort (ObjectSortVariable (Id "s1"))]
                , symbolSentenceReturnSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , symbolSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        , Success "symbol sy1 {} () : s1 [] "
            SymbolSentence
                { symbolSentenceSymbol = ObjectSymbol
                    { objectSymbolConstructor = Id "sy1"
                    , objectSymbolParams = []
                    }
                , symbolSentenceSorts = []
                , symbolSentenceReturnSort =
                    ObjectSortVariableSort (ObjectSortVariable (Id "s1"))
                , symbolSentenceAttributes = Attributes []
                }
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
            (Attributes [StringLiteralPattern (StringLiteral "a")])
        , Success "[]"
            (Attributes [])
        , Success "[\"a\", \"b\"]"
            (Attributes
                [ StringLiteralPattern (StringLiteral "a")
                , StringLiteralPattern (StringLiteral "b")
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
                        , sortSentenceSort =
                            ObjectSortVariableSort (ObjectSortVariable (Id "c"))
                        , sortSentenceAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        , Success "module MN sort{}c[] sort{}c[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ SortSentence
                        { sortSentenceParameters = []
                        , sortSentenceSort =
                            ObjectSortVariableSort (ObjectSortVariable (Id "c"))
                        , sortSentenceAttributes = Attributes []
                        }
                    , SortSentence
                        { sortSentenceParameters = []
                        , sortSentenceSort =
                            ObjectSortVariableSort (ObjectSortVariable (Id "c"))
                        , sortSentenceAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        , FailureWithoutMessage
            [ ""
            , "module MN endmodule []"
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
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                , definitionModules =
                    Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ SortSentence
                                { sortSentenceParameters = []
                                , sortSentenceSort =
                                    ObjectSortVariableSort
                                        (ObjectSortVariable (Id "c"))
                                , sortSentenceAttributes = Attributes []
                                }
                            ]
                        , moduleAttributes =
                            Attributes
                                [StringLiteralPattern (StringLiteral "b")]
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
