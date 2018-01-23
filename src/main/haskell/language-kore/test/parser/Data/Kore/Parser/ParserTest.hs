module Data.Kore.Parser.ParserTest (koreParserTests) where

import           Test.Tasty

import           Data.Kore.AST
import           Data.Kore.Parser.ParserImpl
import           Data.Kore.Parser.ParserTestUtils

koreParserTests :: TestTree
koreParserTests =
    testGroup
        "Parser Tests"
        [ testGroup "objectSortParser" objectSortParserTests
        , testGroup "metaSortConverter" metaSortConverterTests
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
        , testGroup "sentenceAliasParser" sentenceAliasParserTests
        , testGroup "sentenceAxiomParser" sentenceAxiomParserTests
        , testGroup "sentenceSortParser" sentenceSortParserTests
        , testGroup "sentenceSymbolParser" sentenceSymbolParserTests
        , testGroup "attributesParser" attributesParserTests
        , testGroup "moduleParser" moduleParserTests
        , testGroup "definitionParser" definitionParserTests
        ]

objectSortParserTests :: [TestTree]
objectSortParserTests =
    parseTree (sortParser Object)
        [ Success "var" $
            SortVariableSort ( SortVariable (Id "var") )
        , Success "sort1{}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts = []
                }
        , Success "sort1{sort2}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts =
                    [ SortVariableSort ( SortVariable (Id "sort2") ) ]
                }
        , Success "sort1{sort2, sort3}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts =
                    [ SortVariableSort ( SortVariable (Id "sort2") )
                    , SortVariableSort ( SortVariable (Id "sort3") )
                    ]
                }
        , Success "sort1{sort2{sort3}}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts =
                    [ SortActualSort SortActual
                        { sortActualName = Id "sort2"
                        , sortActualSorts =
                            [ SortVariableSort (SortVariable (Id "sort3")) ]
                        }
                    ]
                }
        , FailureWithoutMessage ["var1, var2", "var1{var1 var2}"]
        ]

metaSortConverterTests :: [TestTree]
metaSortConverterTests =
    parseTree (sortParser Meta)
        [ Success "#var"
            (SortVariableSort (SortVariable (Id "#var")))
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
                "Failed reading: metaSortConverter: " ++
                "Invalid constructor: '#Chart'."
            }
        , Failure
            { failureInput = "#Char{#Char}"
            , failureExpected =
                "Failed reading: metaSortConverter: Non empty parameter sorts."
            }
        , FailureWithoutMessage
            [ "var1, var2", "var1{var1 var2}"
            , "sort1{sort2, sort3}", "sort1{sort2{sort3}}"
            ]
        ]

objectSortListParserTests :: [TestTree]
objectSortListParserTests =
    parseTree (inParenthesesSortListParser Object)
        [ Success "()" []
        , Success "(var)"
            [ sortVariableSort "var" ]
        , Success "( var1  , var2   )  "
            [ sortVariableSort "var1"
            , sortVariableSort "var2"
            ]
        , Success "(sort1{sort2}, var)"
            [ SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts =
                    [ sortVariableSort "sort2" ]
                }
            , sortVariableSort "var"
            ]
        , FailureWithoutMessage ["(var1 var2)"]
        ]

metaSortListParserTests :: [TestTree]
metaSortListParserTests =
    parseTree (inCurlyBracesSortListParser Meta)
        [ Success "{}" []
        , Success "{#var}"
            [SortVariableSort (SortVariable (Id "#var"))]
        , Success "{#var1, #var2}"
            [ SortVariableSort (SortVariable (Id "#var1"))
            , SortVariableSort (SortVariable (Id "#var2"))
            ]
        , Success "{#Char{  }  , #var}"
            [ metaSort CharSort
            , SortVariableSort (SortVariable (Id "#var"))
            ]
        , FailureWithoutMessage
            [ "{#var1 #var2}", "{#var1, var2}" ]
        ]

objectSortVariableParserTests :: [TestTree]
objectSortVariableParserTests =
    parseTree (sortVariableParser Object)
        [ Success "var" (SortVariable (Id "var"))
        , FailureWithoutMessage ["", "#", "#var"]
        ]

metaSortVariableParserTests :: [TestTree]
metaSortVariableParserTests =
    parseTree (sortVariableParser Meta)
        [ Success "#var" (SortVariable (Id "#var"))
        , FailureWithoutMessage ["", "#", "var"]
        ]

sortVariableParserTests :: [TestTree]
sortVariableParserTests =
    parseTree unifiedSortVariableParser
        [ Success "var"
            ( ObjectSortVariable
                (SortVariable (Id "var"))
            )
        , Success "#var"
            ( MetaSortVariable
                (SortVariable (Id "#var"))
            )
        , FailureWithoutMessage ["", "#"]
        ]

objectAliasParserTests :: [TestTree]
objectAliasParserTests =
    parseTree (aliasParser Object)
        [ Success "c1{}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams = []
                }
        , Success "c1{s1}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams = [ sortVariableSort "s1" ]
                }
        , Success "c1{s1,s2{s3}}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams =
                    [ sortVariableSort "s1"
                    , SortActualSort SortActual
                        { sortActualName = Id "s2"
                        , sortActualSorts = [ sortVariableSort "s3" ]
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
                { symbolConstructor = Id "c1"
                , symbolParams = []
                }
        , Success "c1{s1}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams = [ sortVariableSort "s1" ]
                }
        , Success "c1{s1,s2{s3}}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams =
                    [ sortVariableSort "s1"
                    , SortActualSort SortActual
                        { sortActualName = Id "s2"
                        , sortActualSorts = [ sortVariableSort "s3" ]
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
                { aliasConstructor = Id "#c1"
                , aliasParams = []
                }
        , Success "#c1{#s1}"
            Alias
                { aliasConstructor = Id "#c1"
                , aliasParams =
                    [SortVariableSort (SortVariable (Id "#s1"))]
                }
        , Success "#c1{#s1,#Char{}}"
            Alias
                { aliasConstructor = Id "#c1"
                , aliasParams =
                    [ SortVariableSort (SortVariable (Id "#s1"))
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
                { symbolConstructor = Id "#c1"
                , symbolParams = []
                }
        , Success "#c1{#s1}"
            Symbol
                { symbolConstructor = Id "#c1"
                , symbolParams =
                    [SortVariableSort (SortVariable (Id "#s1"))]
                }
        , Success "#c1{#s1,#CharList{}}"
            Symbol
                { symbolConstructor = Id "#c1"
                , symbolParams =
                    [ SortVariableSort (SortVariable (Id "#s1"))
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
                { variableName = Id "v"
                , variableSort = sortVariableSort "s"
                }
        , Success "v:s1{s2}"
            Variable
                { variableName = Id "v"
                , variableSort =
                    SortActualSort SortActual
                        { sortActualName = Id "s1"
                        , sortActualSorts = [ sortVariableSort "s2" ]
                        }
                }
        , FailureWithoutMessage ["", "var", "v:", ":s"]
        ]

andPatternParserTests :: [TestTree]
andPatternParserTests =
    parseTree patternParser
        [ Success "\\and{s}(\"a\", \"b\")"
            ( ObjectPattern $ AndPattern And
                { andSort = sortVariableSort "s"
                , andFirst =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , andSecond =
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
        [ Success "#v:#Char"
            ( MetaPattern $ VariablePattern Variable
                { variableName = Id "#v"
                , variableSort = sortVariableSort "#Char"
                }
            )
        , Success "v:s1{s2}"
            ( ObjectPattern $ VariablePattern Variable
                { variableName = Id "v"
                , variableSort =
                    SortActualSort SortActual
                        { sortActualName = Id "s1"
                        , sortActualSorts = [ sortVariableSort "s2" ]
                        }
                }
            )
        , Success "c{s1,s2}(v1:s1, v2:s2)"
            ( ObjectPattern $ ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "c"
                        , symbolOrAliasParams =
                            [ sortVariableSort "s1"
                            , sortVariableSort "s2" ]
                        }
                , applicationPatterns =
                    [ ObjectPattern $ VariablePattern Variable
                        { variableName = Id "v1"
                        , variableSort = sortVariableSort "s1"
                        }
                    , ObjectPattern $ VariablePattern Variable
                        { variableName = Id "v2"
                        , variableSort = sortVariableSort "s2"
                        }
                    ]
                }
            )
        , Success "c{}()"
            ( ObjectPattern $ ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "c"
                        , symbolOrAliasParams = []
                        }
                , applicationPatterns = []
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree patternParser
        [ Success "\\bottom{#Sort}()"
            (MetaPattern $ BottomPattern (sortVariableSort "#Sort"))
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
            (ObjectPattern $ CeilPattern Ceil
                    { ceilOperandSort = sortVariableSort "s1"
                    , ceilResultSort = sortVariableSort "s2"
                    , ceilPattern =
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
            ( ObjectPattern $ EqualsPattern Equals
                    { equalsOperandSort = sortVariableSort "s1"
                    , equalsResultSort = sortVariableSort "s2"
                    , equalsFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , equalsSecond =
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
        [ Success "\\exists{s}(#v:#Char, \"b\")"
            (ObjectPattern $ ExistsPattern Exists
                    { existsSort = sortVariableSort "s"
                    , existsVariable = MetaVariable
                        Variable
                            { variableName = Id "#v"
                            , variableSort = sortVariableSort "#Char"
                            }
                    , existsPattern =
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
            ( ObjectPattern $ FloorPattern Floor
                    { floorOperandSort = sortVariableSort "s1"
                    , floorResultSort = sortVariableSort "s2"
                    , floorPattern =
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
            ( ObjectPattern $ ForallPattern Forall
                    { forallSort = sortVariableSort "s"
                    , forallVariable = ObjectVariable
                        Variable
                            { variableName = Id "v"
                            , variableSort = sortVariableSort "s1"
                            }
                    , forallPattern =
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
            ( ObjectPattern $ IffPattern Iff
                    { iffSort = sortVariableSort "s"
                    , iffFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , iffSecond =
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
            ( ObjectPattern $ ImpliesPattern Implies
                    { impliesSort = sortVariableSort "s"
                    , impliesFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , impliesSecond =
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
            ( ObjectPattern $ MemPattern $ Mem
                    { memOperandSort = sortVariableSort "s1"
                    , memResultSort = sortVariableSort "s2"
                    , memVariable = ObjectVariable
                        Variable
                            { variableName = Id "v"
                            , variableSort = sortVariableSort "s3"
                            }
                    , memPattern =
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
            ( ObjectPattern $ NotPattern Not
                    { notSort = sortVariableSort "s"
                    , notPattern =
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
            ( ObjectPattern $ OrPattern Or
                    { orSort = sortVariableSort "s"
                    , orFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , orSecond =
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
            (ObjectPattern $ TopPattern (sortVariableSort "s"))
        , FailureWithoutMessage
            ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"]
        ]
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
    parseTree patternParser
        [ Success "v:s"
            ( ObjectPattern $ VariablePattern Variable
                { variableName = Id "v"
                , variableSort = sortVariableSort "s"
                }
            )
        , Success "v:s1{s2}"
            ( ObjectPattern $ VariablePattern Variable
                { variableName = Id "v"
                , variableSort =
                    SortActualSort SortActual
                        { sortActualName=Id "s1"
                        , sortActualSorts = [ sortVariableSort "s2" ]
                        }
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]

sentenceAliasParserTests :: [TestTree]
sentenceAliasParserTests =
    parseTree sentenceParser
        [ Success "alias a{s1}(s2):s3[\"a\"]"
            ( ObjectSentenceAliasSentence
                SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id "a"
                        , aliasParams = [ sortVariableSort "s1" ]
                        }
                    , sentenceAliasSorts = [ sortVariableSort "s2"]
                    , sentenceAliasReturnSort = sortVariableSort "s3"
                    , sentenceAliasAttributes =
                        Attributes
                            [MetaPattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
            )
        , Success "alias a { s1 , s2 } ( s3, s4 ) : s5 [ \"a\" , \"b\" ]"
            ( ObjectSentenceAliasSentence
                SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id "a"
                        , aliasParams =
                            [ sortVariableSort "s1"
                            , sortVariableSort "s2"
                            ]
                        }
                    , sentenceAliasSorts =
                        [ sortVariableSort "s3"
                        , sortVariableSort "s4"
                        ]
                    , sentenceAliasReturnSort = sortVariableSort "s5"
                    , sentenceAliasAttributes =
                        Attributes
                            [ MetaPattern $
                                StringLiteralPattern (StringLiteral "a")
                            , MetaPattern $
                                StringLiteralPattern (StringLiteral "b")
                            ]
                    }
            )
        , Success "alias #a{}():#Char[]"
            ( MetaSentenceAliasSentence
                SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id "#a"
                        , aliasParams = []
                        }
                    , sentenceAliasSorts = []
                    , sentenceAliasReturnSort = sortVariableSort "#Char"
                    , sentenceAliasAttributes = Attributes []
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

sentenceAxiomParserTests :: [TestTree]
sentenceAxiomParserTests =
    parseTree sentenceParser
        [ Success "axiom{sv1}\"a\"[\"b\"]"
            ( SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ObjectSortVariable
                        (SortVariable (Id "sv1"))]
                , sentenceAxiomPattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , sentenceAxiomAtrributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "axiom{}\"a\"[\"b\"]"
            ( SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , sentenceAxiomAtrributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
            )
        , Success "axiom { sv1 , sv2 } \"a\" [ \"b\" ] "
            ( SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ ObjectSortVariable
                        (SortVariable (Id "sv1"))
                    , ObjectSortVariable
                        (SortVariable (Id "sv2"))
                    ]
                , sentenceAxiomPattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , sentenceAxiomAtrributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
            )
        , FailureWithoutMessage
            [ ""
            , "{sv1}\"a\"[\"b\"]"
            , "axiom\"a\"[\"b\"]"
            -- , "axiom{}\"a\"[\"b\"]" See the TODO above.
            , "axiom{sv1}[\"b\"]"
            , "axiom{sv1}\"a\""
            ]
        ]

sentenceSortParserTests :: [TestTree]
sentenceSortParserTests =
    parseTree sentenceParser
        [ Success "sort { sv1 } s1 [ \"a\" ]"
            ( SentenceSortSentence SentenceSort
                { sentenceSortParameters =
                    [ ObjectSortVariable
                        (SortVariable (Id "sv1"))
                    ]
                , sentenceSortSort = sortVariableSort "s1"
                , sentenceSortAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , Success "sort {} s1 [ \"a\" ]"
            ( SentenceSortSentence SentenceSort
                { sentenceSortParameters = []
                , sentenceSortSort = sortVariableSort "s1"
                , sentenceSortAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
            )
        , FailureWithoutMessage
            [ ""
            , "{ sv1 } s1 [ \"a\" ]"
            , "sort s1 [ \"a\" ]"
            , "sort { sv1 } [ \"a\" ]"
            , "sort { sv1 } s1 "
            ]
        ]

sentenceSymbolParserTests :: [TestTree]
sentenceSymbolParserTests =
    parseTree sentenceParser
        [ Success "symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( ObjectSentenceSymbolSentence
                SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id "sy1"
                        , symbolParams = [ sortVariableSort "s1" ]
                        }
                    , sentenceSymbolSorts = [ sortVariableSort "s1" ]
                    , sentenceSymbolReturnSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes =
                        Attributes
                            [MetaPattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
            )
        , Success "symbol sy1 {} () : s1 [] "
            ( ObjectSentenceSymbolSentence
                SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id "sy1"
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts = []
                    , sentenceSymbolReturnSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes = Attributes []
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
                    [ SentenceSortSentence SentenceSort
                        { sentenceSortParameters = []
                        , sentenceSortSort = sortVariableSort "c"
                        , sentenceSortAttributes = Attributes []
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
                    [ SentenceSortSentence SentenceSort
                        { sentenceSortParameters = []
                        , sentenceSortSort = sortVariableSort "c"
                        , sentenceSortAttributes = Attributes []
                        }
                    , SentenceSortSentence SentenceSort
                        { sentenceSortParameters = []
                        , sentenceSortSort = sortVariableSort "c"
                        , sentenceSortAttributes = Attributes []
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
                            [ SentenceSortSentence SentenceSort
                                { sentenceSortParameters = []
                                , sentenceSortSort = sortVariableSort "c"
                                , sentenceSortAttributes = Attributes []
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

sortVariableSort :: String -> Sort a
sortVariableSort name =
    SortVariableSort (SortVariable (Id name))

metaSort :: MetaSortType -> Sort Meta
metaSort sortType =
    SortActualSort SortActual
        { sortActualName = Id (show sortType)
        , sortActualSorts = []}
