module KoreParserTest (koreParserTests) where

import           Test.Tasty

import           KoreAST
import           KoreParserImpl
import           ParserTestUtils

koreParserTests :: TestTree
koreParserTests =
    testGroup
        "Parser Tests"
        [ testGroup "sortParser" sortParserTests
        , testGroup "sortListParser" sortListParserTests
        , testGroup "sortVariableParser" sortVariableParserTests
        , testGroup "sortVariableList1Parser" sortVariableList1ParserTests
        , testGroup "aliasParser" aliasParserTests
        , testGroup "symbolParser" symbolParserTests
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

sortVariableParserTests :: [TestTree]
sortVariableParserTests =
    parseTree sortVariableParser
        [ Success "var" (SortVariable (Id "var"))
        , Success "#var" (SortVariable (Id "#var"))
        ]
        (Failure ["", "#"])

sortVariableList1ParserTests :: [TestTree]
sortVariableList1ParserTests =
    parseTree sortVariableList1Parser
        [ Success "v" [SortVariable (Id "v")]
        , Success "v1, v2" [SortVariable (Id "v1"), SortVariable (Id "v2")]
        ]
        (Failure ["", "v v"])

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
            [ ""
            , "\\and{s,s}(\"a\", \"b\")"
            , "\\and{}(\"a\", \"b\")"
            , "\\and{s}(\"a\")"
            , "\\and{s}(\"a\", \"b\", \"c\")"
            , "\\and{s}(\"a\" \"b\")"
            ])
applicationPatternParserTests :: [TestTree]
applicationPatternParserTests =
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
            , "\\bottom{s}"
            ])
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
equalsPatternParserTests :: [TestTree]
equalsPatternParserTests =
    parseTree patternParser
        [ Success "\\equals{s1, s2}(\"a\", \"b\")"
            EqualsPattern
                { equalsPatternFirstSort =
                    SortVariableSort (SortVariable (Id "s1"))
                , equalsPatternSecondSort =
                    SortVariableSort (SortVariable (Id "s2"))
                , equalsPatternFirst = StringLiteralPattern (StringLiteral "a")
                , equalsPatternSecond = StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
            [ ""
            , "\\equals{s}(\"a\", \"b\")"
            , "\\equals{s,s,s}(\"a\", \"b\")"
            , "\\equals{s,s}(\"a\")"
            , "\\equals{s,s}(\"a\", \"b\", \"c\")"
            , "\\equals{s,s}(\"a\" \"b\")"
            ])
existsPatternParserTests :: [TestTree]
existsPatternParserTests =
    parseTree patternParser
        [ Success "\\exists{s}(v:s1, \"b\")"
            ExistsPattern
                { existsPatternSort =
                    SortVariableSort (SortVariable (Id "s"))
                , existsPatternVariable = Variable
                    { variableName = Id "v"
                    , variableSort = SortVariableSort (SortVariable (Id "s1"))
                    }
                , existsPatternPattern =
                    StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
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
            ])
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
forallPatternParserTests :: [TestTree]
forallPatternParserTests =
    parseTree patternParser
        [ Success "\\forall{s}(v:s1, \"b\")"
            ForallPattern
                { forallPatternSort =
                    SortVariableSort (SortVariable (Id "s"))
                , forallPatternVariable = Variable
                    { variableName = Id "v"
                    , variableSort = SortVariableSort (SortVariable (Id "s1"))
                    }
                , forallPatternPattern =
                    StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
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
            [ ""
            , "\\iff{s,s}(\"a\", \"b\")"
            , "\\iff{}(\"a\", \"b\")"
            , "\\iff{s}(\"a\")"
            , "\\iff{s}(\"a\", \"b\", \"c\")"
            , "\\iff{s}(\"a\" \"b\")"])
impliesPatternParserTests :: [TestTree]
impliesPatternParserTests =
    parseTree patternParser
        [ Success "\\implies{s}(\"a\", \"b\")"
            ImpliesPattern
                { impliesPatternSort = SortVariableSort (SortVariable (Id "s"))
                , impliesPatternFirst = StringLiteralPattern (StringLiteral "a")
                , impliesPatternSecond =
                    StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
            [ ""
            , "\\implies{s,s}(\"a\", \"b\")"
            , "\\implies{}(\"a\", \"b\")"
            , "\\implies{s}(\"a\")"
            , "\\implies{s}(\"a\", \"b\", \"c\")"
            , "\\implies{s}(\"a\" \"b\")"])
memPatternParserTests :: [TestTree]
memPatternParserTests =
    parseTree patternParser
        [ Success "\\mem{s1,s2}(v:s3, \"b\")"
            MemPattern
                { memPatternFirstSort =
                    SortVariableSort (SortVariable (Id "s1"))
                , memPatternSecondSort =
                    SortVariableSort (SortVariable (Id "s2"))
                , memPatternVariable = Variable
                    { variableName = Id "v"
                    , variableSort = SortVariableSort (SortVariable (Id "s3"))
                    }
                , memPatternPattern =
                    StringLiteralPattern (StringLiteral "b")
                }
        ]
        (Failure
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
            ])
notPatternParserTests :: [TestTree]
notPatternParserTests =
    parseTree patternParser
        [ Success "\\not{s}(\"a\")"
            NotPattern
                { notPatternSort = SortVariableSort (SortVariable (Id "s"))
                , notPatternPattern = StringLiteralPattern (StringLiteral "a")
                }
        ]
        (Failure
            [ ""
            , "\\not{s,s}(\"a\")"
            , "\\not{}(\"a\")"
            , "\\not{s}()"
            , "\\not{s}(\"a\", \"b\")"
            , "\\not{s}"
            , "\\not(\"a\")"
            ])
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
            [ ""
            , "\\or{s,s}(\"a\", \"b\")"
            , "\\or{}(\"a\", \"b\")"
            , "\\or{s}(\"a\")"
            , "\\or{s}(\"a\", \"b\", \"c\")"
            , "\\or{s}(\"a\" \"b\")"])
stringLiteralPatternParserTests :: [TestTree]
stringLiteralPatternParserTests =
    parseTree patternParser
        [ Success "\"hello\"" (StringLiteralPattern (StringLiteral "hello"))
        , Success "\"\"" (StringLiteralPattern (StringLiteral ""))
        , Success "\"\\\"\"" (StringLiteralPattern (StringLiteral "\""))
        ]
        (Failure ["", "\""])
topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree patternParser
        [ Success "\\top{s}()"
            (TopPattern (SortVariableSort (SortVariable (Id "s"))))
        ]
        (Failure ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"])
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
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
        ]
        (Failure ["", "var", "v:", ":s", "c(s)", "c{s}"])

aliasSentenceParserTests :: [TestTree]
aliasSentenceParserTests =
    parseTree sentenceParser
        [ Success "alias a{s1}(s2):s3[\"a\"]"
            AliasSentence
                { aliasSentenceAlias = Alias
                    { aliasConstructor = Id "a"
                    , aliasParams = [SortVariableSort (SortVariable (Id "s1"))]
                    }
                , aliasSentenceSorts =
                    [SortVariableSort (SortVariable (Id "s2"))]
                , aliasSentenceReturnSort =
                    SortVariableSort (SortVariable (Id "s3"))
                , aliasSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        , Success "alias a { s1 , s2 } ( s3, s4 ) : s5 [ \"a\" , \"b\" ]"
            AliasSentence
                { aliasSentenceAlias = Alias
                    { aliasConstructor = Id "a"
                    , aliasParams =
                        [ SortVariableSort (SortVariable (Id "s1"))
                        , SortVariableSort (SortVariable (Id "s2"))
                        ]
                    }
                , aliasSentenceSorts =
                    [ SortVariableSort (SortVariable (Id "s3"))
                    , SortVariableSort (SortVariable (Id "s4"))
                    ]
                , aliasSentenceReturnSort =
                    SortVariableSort (SortVariable (Id "s5"))
                , aliasSentenceAttributes =
                    Attributes
                        [ StringLiteralPattern (StringLiteral "a")
                        , StringLiteralPattern (StringLiteral "b")
                        ]
                }
        , Success "alias a{}():s3[]"
            AliasSentence
                { aliasSentenceAlias = Alias
                    { aliasConstructor = Id "a"
                    , aliasParams = []
                    }
                , aliasSentenceSorts = []
                , aliasSentenceReturnSort =
                    SortVariableSort (SortVariable (Id "s3"))
                , aliasSentenceAttributes = Attributes []
                }
        ]
    (Failure
        [ ""
        , "a{s1}(s2):s3[\"a\"]"
        , "alias {s1}(s2):s3[\"a\"]"
        , "alias a(s2):s3[\"a\"]"
        , "alias a{s1}:s3[\"a\"]"
        , "alias a{s1}(s2)s3[\"a\"]"
        , "alias a{s1}(s2):[\"a\"]"
        , "alias a{s1}(s2)[\"a\"]"
        , "alias a{s1}(s2):s3"
        ])

axiomSentenceParserTests :: [TestTree]
axiomSentenceParserTests =
    parseTree sentenceParser
        [ Success "axiom{sv1}\"a\"[\"b\"]"
            AxiomSentence
                { axiomSentenceParameters = [SortVariable (Id "sv1")]
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
                    [SortVariable (Id "sv1"), SortVariable (Id "sv2")]
                , axiomSentencePattern =
                    StringLiteralPattern (StringLiteral "a")
                , axiomSentenceAtrributes =
                    Attributes [StringLiteralPattern (StringLiteral "b")]
                }
        ]
    (Failure
        [ ""
        , "{sv1}\"a\"[\"b\"]"
        , "axiom\"a\"[\"b\"]"
        -- , "axiom{}\"a\"[\"b\"]" See the TODO above.
        , "axiom{sv1}[\"b\"]"
        , "axiom{sv1}\"a\""
        ])

sortSentenceParserTests :: [TestTree]
sortSentenceParserTests =
    parseTree sentenceParser
        [ Success "sort { sv1 } s1 [ \"a\" ]"
            SortSentence
                { sortSentenceParameters = [SortVariable (Id "sv1")]
                , sortSentenceSort = SortVariableSort (SortVariable (Id "s1"))
                , sortSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "sort {} s1 [ \"a\" ]"
            SortSentence
                { sortSentenceParameters = []
                , sortSentenceSort = SortVariableSort (SortVariable (Id "s1"))
                , sortSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
         ]
    (Failure
        [ ""
        , "{ sv1 } s1 [ \"a\" ]"
        , "sort s1 [ \"a\" ]"
        , "sort { sv1 } [ \"a\" ]"
        , "sort { sv1 } s1 "
        ])

symbolSentenceParserTests :: [TestTree]
symbolSentenceParserTests =
    parseTree sentenceParser
        [ Success "symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            SymbolSentence
                { symbolSentenceSymbol = Symbol
                    { symbolConstructor = Id "sy1"
                    , symbolParams = [SortVariableSort (SortVariable (Id "s1"))]
                    }
                , symbolSentenceSorts =
                    [SortVariableSort (SortVariable (Id "s1"))]
                , symbolSentenceReturnSort =
                    SortVariableSort (SortVariable (Id "s1"))
                , symbolSentenceAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        , Success "symbol sy1 {} () : s1 [] "
            SymbolSentence
                { symbolSentenceSymbol = Symbol
                    { symbolConstructor = Id "sy1"
                    , symbolParams = []
                    }
                , symbolSentenceSorts = []
                , symbolSentenceReturnSort =
                    SortVariableSort (SortVariable (Id "s1"))
                , symbolSentenceAttributes = Attributes []
                }
        ]
    (Failure
        [ ""
        , "sy1 { s1 } ( s1 ) : s1 [\"a\"] "
        , "symbol { s1 } ( s1 ) : s1 [\"a\"] "
        , "symbol sy1 ( s1 ) : s1 [\"a\"] "
        , "symbol sy1 { s1 } : s1 [\"a\"] "
        , "symbol sy1 { s1 } ( s1 ) s1 [\"a\"] "
        , "symbol sy1 { s1 } ( s1 ) : [\"a\"] "
        , "symbol sy1 { s1 } ( s1 ) : s1 "
        , "symbol sy1 { s1 } ( s1 ) [\"a\"] "
        ])

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
        ]
    (Failure ["", "a", "\"a\"", "[\"a\" \"a\"]"])


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
                            SortVariableSort (SortVariable (Id "c"))
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
                            SortVariableSort (SortVariable (Id "c"))
                        , sortSentenceAttributes = Attributes []
                        }
                    , SortSentence
                        { sortSentenceParameters = []
                        , sortSentenceSort =
                            SortVariableSort (SortVariable (Id "c"))
                        , sortSentenceAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes [StringLiteralPattern (StringLiteral "a")]
                }
        ]
    (Failure
        [ ""
        , "module MN endmodule []"
        , "MN sort{}c[] endmodule [\"a\"]"
        , "module sort{}c[] endmodule [\"a\"]"
        , "module MN sort{}c[] [\"a\"]"
        , "module MN sort{}c[] endmodule"
        ])

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
                                    SortVariableSort (SortVariable (Id "c"))
                                , sortSentenceAttributes = Attributes []
                                }
                            ]
                        , moduleAttributes =
                            Attributes
                                [StringLiteralPattern (StringLiteral "b")]
                        }
                }
        ]
    (Failure
        [ ""
        , "[]"
        , "module M sort{}c[] endmodule [\"b\"]"
        , "[\"a\"] module M sort{}c[] endmodule [\"b\"] "
            ++ "module O sort{}c[] endmodule [\"c\"]"
        ])

------------------------------------
-- Generic test utilities
------------------------------------
