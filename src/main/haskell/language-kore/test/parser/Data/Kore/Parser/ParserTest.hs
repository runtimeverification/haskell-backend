module Data.Kore.Parser.ParserTest (koreParserTests) where

import           Test.Tasty                       (TestTree, testGroup)

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
        , testGroup
            "objectInCurlyBracesSortVariableListParser"
            objectInCurlyBracesSortVariableListParserTest
        , testGroup
            "metaInCurlyBracesSortVariableListParser"
            metaInCurlyBracesSortVariableListParserTest
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
        , testGroup "nextPatternParser" nextPatternParserTests
        , testGroup "notPatternParser" notPatternParserTests
        , testGroup "orPatternParser" orPatternParserTests
        , testGroup "rewritesPatternParser" rewritesPatternParserTests
        , testGroup "stringLiteralPatternParser" stringLiteralPatternParserTests
        , testGroup "topPatternParser" topPatternParserTests
        , testGroup "variablePatternParser" variablePatternParserTests
        , testGroup "sentenceAliasParser" sentenceAliasParserTests
        , testGroup "sentenceImportParser" sentenceImportParserTests
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
        [ success "var" $
            SortVariableSort ( SortVariable (Id "var") )
        , success "sort1{}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts = []
                }
        , success "sort1{sort2}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts =
                    [ SortVariableSort ( SortVariable (Id "sort2") ) ]
                }
        , success "sort1{sort2, sort3}" $
            SortActualSort SortActual
                { sortActualName = Id "sort1"
                , sortActualSorts =
                    [ SortVariableSort ( SortVariable (Id "sort2") )
                    , SortVariableSort ( SortVariable (Id "sort3") )
                    ]
                }
        , success "sort1{sort2{sort3}}" $
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
        [ success "#var"
            (SortVariableSort (SortVariable (Id "#var")))
        , success "#Char{}" (metaSort CharSort)
        , success "#CharList{}" (metaSort CharListSort)
        , success "#Pattern{}" (metaSort PatternSort)
        , success "#PatternList{}" (metaSort PatternListSort)
        , success "#Sort{}" (metaSort SortSort)
        , success "#SortList{}" (metaSort SortListSort)
        , success "#String{}" (metaSort StringSort)
        , success "#Symbol{}" (metaSort SymbolSort)
        , success "#SymbolList{}" (metaSort SymbolListSort)
        , success "#Variable{}" (metaSort VariableSort)
        , success "#VariableList{}" (metaSort VariableListSort)
        , Failure FailureTest
            { failureInput = "#Chart{}"
            , failureExpected =
                "Failed reading: metaSortConverter: " ++
                "Invalid constructor: '#Chart'."
            }
        , Failure FailureTest
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
        [ success "()" []
        , success "(var)"
            [ sortVariableSort "var" ]
        , success "( var1  , var2   )  "
            [ sortVariableSort "var1"
            , sortVariableSort "var2"
            ]
        , success "(sort1{sort2}, var)"
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
        [ success "{}" []
        , success "{#var}"
            [SortVariableSort (SortVariable (Id "#var"))]
        , success "{#var1, #var2}"
            [ SortVariableSort (SortVariable (Id "#var1"))
            , SortVariableSort (SortVariable (Id "#var2"))
            ]
        , success "{#Char{  }  , #var}"
            [ metaSort CharSort
            , SortVariableSort (SortVariable (Id "#var"))
            ]
        , FailureWithoutMessage
            [ "{#var1 #var2}", "{#var1, var2}" ]
        ]

objectSortVariableParserTests :: [TestTree]
objectSortVariableParserTests =
    parseTree (sortVariableParser Object)
        [ success "var" (SortVariable (Id "var"))
        , FailureWithoutMessage ["", "#", "#var"]
        ]

metaSortVariableParserTests :: [TestTree]
metaSortVariableParserTests =
    parseTree (sortVariableParser Meta)
        [ success "#var" (SortVariable (Id "#var"))
        , FailureWithoutMessage ["", "#", "var"]
        ]

objectInCurlyBracesSortVariableListParserTest :: [TestTree]
objectInCurlyBracesSortVariableListParserTest =
    parseTree (inCurlyBracesSortVariableListParser Object)
        [ success "{}" []
        , success "{var}"
            [ SortVariable (Id "var") ]
        , success "{var1, var2}"
            [ SortVariable (Id "var1")
            , SortVariable (Id "var2")
            ]
        , FailureWithoutMessage
            [ "{var1 var2}", "{#var1, var2}", "{var, Int{}}" ]
        ]

metaInCurlyBracesSortVariableListParserTest :: [TestTree]
metaInCurlyBracesSortVariableListParserTest =
    parseTree (inCurlyBracesSortVariableListParser Meta)
        [ success "{}" []
        , success "{#var}"
            [ SortVariable (Id "#var") ]
        , success "{#var1, #var2}"
            [ SortVariable (Id "#var1")
            , SortVariable (Id "#var2")
            ]
        , FailureWithoutMessage
            [ "{#var1 #var2}", "{#var1, var2}", "{#var, #Char{}}" ]
        ]

sortVariableParserTests :: [TestTree]
sortVariableParserTests =
    parseTree unifiedSortVariableParser
        [ success "var"
            ( ObjectSortVariable
                (SortVariable (Id "var"))
            )
        , success "#var"
            ( MetaSortVariable
                (SortVariable (Id "#var"))
            )
        , FailureWithoutMessage ["", "#"]
        ]

objectAliasParserTests :: [TestTree]
objectAliasParserTests =
    parseTree (aliasParser Object)
        [ success "c1{}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams = []
                }
        , success "c1{s1}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams = [ sortVariable "s1" ]
                }
        , success "c1{s1,s2}"
            Alias
                { aliasConstructor = Id "c1"
                , aliasParams =
                    [ sortVariable "s1"
                    , sortVariable "s2"
                    ]
                }
        , FailureWithoutMessage
            ["alias", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}", "c1{s1{}}"]
        ]

objectSymbolParserTests :: [TestTree]
objectSymbolParserTests =
    parseTree (symbolParser Object)
        [ success "c1{}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams = []
                }
        , success "c1{s1}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams = [ sortVariable "s1" ]
                }
        , success "c1{s1,s2}"
            Symbol
                { symbolConstructor = Id "c1"
                , symbolParams =
                    [ sortVariable "s1"
                    , sortVariable "s2"
                    ]
                }
        , FailureWithoutMessage
            ["symbol", "a1{a2},a1{a2}", "a1{a2 a2}", "a1{a2}a1{a2}", "c1{s1{}}"]
        ]

metaAliasParserTests :: [TestTree]
metaAliasParserTests =
    parseTree (aliasParser Meta)
        [ success "#c1{}"
            Alias
                { aliasConstructor = Id "#c1"
                , aliasParams = []
                }
        , success "#c1{#s1}"
            Alias
                { aliasConstructor = Id "#c1"
                , aliasParams = [sortVariable "#s1"]
                }
        , success "#c1{#s1,#s2}"
            Alias
                { aliasConstructor = Id "#c1"
                , aliasParams =
                    [ sortVariable "#s1"
                    , sortVariable "#s2"
                    ]
                }
        , FailureWithoutMessage
            [ "#alias", "#a1{#a2},#a1{#a2}", "#a1{#a2 #a2}", "#a1{#a2}#a1{#a2}"
            , "#c1{#Char{}}"
            ]
        ]

metaSymbolParserTests :: [TestTree]
metaSymbolParserTests =
    parseTree (symbolParser Meta)
        [ success "#c1{}"
            Symbol
                { symbolConstructor = Id "#c1"
                , symbolParams = []
                }
        , success "#c1{#s1}"
            Symbol
                { symbolConstructor = Id "#c1"
                , symbolParams = [sortVariable "#s1"]
                }
        , success "#c1{#s1,#s2}"
            Symbol
                { symbolConstructor = Id "#c1"
                , symbolParams =
                    [ sortVariable "#s1"
                    , sortVariable "#s2"
                    ]
                }
        , FailureWithoutMessage
            [ "#symbol", "#a1{#a2},#a1{#a2}", "#a1{#a2 #a2}", "#a1{#a2}#a1{#a2}"
            , "#c1{#Char{}}"
            ]
        ]

variableParserTests :: [TestTree]
variableParserTests =
    parseTree (variableParser Object)
        [ success "v:s"
            Variable
                { variableName = Id "v"
                , variableSort = sortVariableSort "s"
                }
        , success "v:s1{s2}"
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
        [ success "\\and{s}(\"a\", \"b\")"
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
        [ success "#v:#Char"
            ( MetaPattern $ VariablePattern Variable
                { variableName = Id "#v"
                , variableSort = sortVariableSort "#Char"
                }
            )
        , success "v:s1{s2}"
            ( ObjectPattern $ VariablePattern Variable
                { variableName = Id "v"
                , variableSort =
                    SortActualSort SortActual
                        { sortActualName = Id "s1"
                        , sortActualSorts = [ sortVariableSort "s2" ]
                        }
                }
            )
        , success "c{s1,s2}(v1:s1, v2:s2)"
            ( ObjectPattern $ ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "c"
                        , symbolOrAliasParams =
                            [ sortVariableSort "s1"
                            , sortVariableSort "s2" ]
                        }
                , applicationChildren =
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
        , success "c{}()"
            ( ObjectPattern $ ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "c"
                        , symbolOrAliasParams = []
                        }
                , applicationChildren = []
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree patternParser
        [ success "\\bottom{#Sort}()"
            (MetaPattern $ BottomPattern $ Bottom (sortVariableSort "#Sort"))
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
        [ success "\\ceil{s1, s2}(\"a\")"
            (ObjectPattern $ CeilPattern Ceil
                    { ceilOperandSort = sortVariableSort "s1"
                    , ceilResultSort = sortVariableSort "s2"
                    , ceilChild =
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
        [ success "\\equals{s1, s2}(\"a\", \"b\")"
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
        [ success "\\exists{s}(#v:#Char, \"b\")"
            (ObjectPattern $ ExistsPattern Exists
                    { existsSort = sortVariableSort "s"
                    , existsVariable = MetaVariable
                        Variable
                            { variableName = Id "#v"
                            , variableSort = sortVariableSort "#Char"
                            }
                    , existsChild =
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
        [ success "\\floor{s1, s2}(\"a\")"
            ( ObjectPattern $ FloorPattern Floor
                    { floorOperandSort = sortVariableSort "s1"
                    , floorResultSort = sortVariableSort "s2"
                    , floorChild =
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
        [ success "\\forall{s}(v:s1, \"b\")"
            ( ObjectPattern $ ForallPattern Forall
                    { forallSort = sortVariableSort "s"
                    , forallVariable = ObjectVariable
                        Variable
                            { variableName = Id "v"
                            , variableSort = sortVariableSort "s1"
                            }
                    , forallChild =
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
        [ success "\\iff{s}(\"a\", \"b\")"
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
        [ success "\\implies{s}(\"a\", \"b\")"
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
        [ success "\\in{s1,s2}(v:s3, \"b\")"
            ( ObjectPattern $ InPattern In
                    { inOperandSort = sortVariableSort "s1"
                    , inResultSort = sortVariableSort "s2"
                    , inContainedChild = ObjectPattern $
                        VariablePattern Variable
                            { variableName = Id "v"
                            , variableSort = sortVariableSort "s3"
                            }
                    , inContainingChild =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , success "\\in{s1,s2}(\"a\", \"b\")"
            ( ObjectPattern $ InPattern In
                    { inOperandSort = sortVariableSort "s1"
                    , inResultSort = sortVariableSort "s2"
                    , inContainedChild =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , inContainingChild =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , FailureWithoutMessage
            [ ""
            , "\\mem{s1,s2}(v:s3, \"b\")"
            , "\\in{s}(v:s1, \"b\")"
            , "\\in{s,s,s}(v:s1, \"b\")"
            , "\\in{s,s}(, \"b\")"
            , "\\in{s,s}(\"b\")"
            , "\\in{s,s}(v:s1, )"
            , "\\in{s,s}(v:s1)"
            , "\\in{s,s}()"
            , "\\in{s,s}"
            , "\\in"
            , "\\in(v:s1, \"b\")"
            ]
        ]
notPatternParserTests :: [TestTree]
notPatternParserTests =
    parseTree patternParser
        [ success "\\not{s}(\"a\")"
            ( ObjectPattern $ NotPattern Not
                    { notSort = sortVariableSort "s"
                    , notChild =
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
nextPatternParserTests :: [TestTree]
nextPatternParserTests =
    parseTree patternParser
        [ success "\\next{s}(\"a\")"
            ( ObjectPattern $ NextPattern Next
                    { nextSort = sortVariableSort "s"
                    , nextChild =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    }
            )
        , Failure FailureTest
            { failureInput = "\\next{#s}(\"a\")"
            , failureExpected =
                "Failed reading: Cannot have a \\next meta pattern."
            }
        , FailureWithoutMessage
            [ ""
            , "\\next{s,s}(\"a\")"
            , "\\next{}(\"a\")"
            , "\\next{s}()"
            , "\\next{s}(\"a\", \"b\")"
            , "\\next{s}"
            , "\\next(\"a\")"
            ]
        ]
orPatternParserTests :: [TestTree]
orPatternParserTests =
    parseTree patternParser
        [ success "\\or{s}(\"a\", \"b\")"
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
rewritesPatternParserTests :: [TestTree]
rewritesPatternParserTests =
    parseTree patternParser
        [ success "\\rewrites{s}(\"a\", \"b\")"
            ( ObjectPattern $ RewritesPattern Rewrites
                    { rewritesSort = sortVariableSort "s"
                    , rewritesFirst =
                        MetaPattern $ StringLiteralPattern (StringLiteral "a")
                    , rewritesSecond =
                        MetaPattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , Failure FailureTest
            { failureInput = "\\rewrites{#s}(\"a\", \"b\")"
            , failureExpected =
                "Failed reading: Cannot have a \\rewrites meta pattern."
            }
        , FailureWithoutMessage
            [ ""
            , "\\rewrites{s,s}(\"a\", \"b\")"
            , "\\rewrites{}(\"a\", \"b\")"
            , "\\rewrites{s}(\"a\")"
            , "\\rewrites{s}(\"a\", \"b\", \"c\")"
            , "\\rewrites{s}(\"a\" \"b\")"]
        ]
stringLiteralPatternParserTests :: [TestTree]
stringLiteralPatternParserTests =
    parseTree patternParser
        [ success "\"hello\""
            (MetaPattern $ StringLiteralPattern (StringLiteral "hello"))
        , success "\"\""
            (MetaPattern $ StringLiteralPattern (StringLiteral ""))
        , success "\"\\\"\""
            (MetaPattern $ StringLiteralPattern (StringLiteral "\""))
        , FailureWithoutMessage ["", "\""]
        ]
topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree patternParser
        [ success "\\top{s}()"
            (ObjectPattern $ TopPattern $ Top (sortVariableSort "s"))
        , FailureWithoutMessage
            ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"]
        ]
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
    parseTree patternParser
        [ success "v:s"
            ( ObjectPattern $ VariablePattern Variable
                { variableName = Id "v"
                , variableSort = sortVariableSort "s"
                }
            )
        , success "v:s1{s2}"
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
        [ success "alias a{s1}(s2):s3[\"a\"]"
            ( ObjectSentenceAliasSentence
                SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id "a"
                        , aliasParams = [ sortVariable "s1" ]
                        }
                    , sentenceAliasSorts = [ sortVariableSort "s2"]
                    , sentenceAliasReturnSort = sortVariableSort "s3"
                    , sentenceAliasAttributes =
                        Attributes
                            [MetaPattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
            )
        , success "alias a { s1 , s2 } ( s3, s4 ) : s5 [ \"a\" , \"b\" ]"
            ( ObjectSentenceAliasSentence
                SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id "a"
                        , aliasParams =
                            [ sortVariable "s1"
                            , sortVariable "s2"
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
        , success "alias #a{}():#Char[]"
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
            , "alias a{s1{}}(s2):s3[\"a\"]"
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
        [ success "axiom{sv1}\"a\"[\"b\"]"
            ( SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ObjectSortVariable
                        (SortVariable (Id "sv1"))]
                , sentenceAxiomPattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , sentenceAxiomAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , success "axiom{}\"a\"[\"b\"]"
            ( SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , sentenceAxiomAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
            )
        , success "axiom { sv1 , sv2 } \"a\" [ \"b\" ] "
            ( SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ ObjectSortVariable
                        (SortVariable (Id "sv1"))
                    , ObjectSortVariable
                        (SortVariable (Id "sv2"))
                    ]
                , sentenceAxiomPattern =
                    MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , sentenceAxiomAttributes =
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

sentenceImportParserTests :: [TestTree]
sentenceImportParserTests =
    parseTree sentenceParser
        [ success "import M[\"b\"]"
            ( SentenceImportSentence SentenceImport
                { sentenceImportModuleName = ModuleName "M"
                , sentenceImportAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "b")]
                }
            )
        , FailureWithoutMessage
            [ ""
            , "M[\"b\"]"
            , "import [\"b\"]"
            , "import M"
            ]
        ]

sentenceSortParserTests :: [TestTree]
sentenceSortParserTests =
    parseTree sentenceParser
        [ success "sort s1 { sv1 } [ \"a\" ]"
            ( SentenceSortSentence SentenceSort
                { sentenceSortName = Id "s1"
                , sentenceSortParameters = [ sortVariable "sv1" ]
                , sentenceSortAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , success "sort s1 {} [ \"a\" ]"
            ( SentenceSortSentence SentenceSort
                { sentenceSortName = Id "s1"
                , sentenceSortParameters = []
                , sentenceSortAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
            )
        , FailureWithoutMessage
            [ ""
            , "s1 { sv1 } [ \"a\" ]"
            , "sort { sv1 } [ \"a\" ]"
            , "sort s1 { sv1{} } [ \"a\" ]"
            , "sort s1 [ \"a\" ]"
            , "sort s1 { sv1 } "
            , "sort { sv1 } s1 [ \"a\" ]"
            ]
        ]

sentenceSymbolParserTests :: [TestTree]
sentenceSymbolParserTests =
    parseTree sentenceParser
        [ success "symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( ObjectSentenceSymbolSentence
                SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id "sy1"
                        , symbolParams = [ sortVariable "s1" ]
                        }
                    , sentenceSymbolSorts = [ sortVariableSort "s1" ]
                    , sentenceSymbolReturnSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes =
                        Attributes
                            [MetaPattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
            )
        , success "symbol sy1 {} () : s1 [] "
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
        [ success "[\"a\"]"
            (Attributes
                [MetaPattern $ StringLiteralPattern (StringLiteral "a")])
        , success "[]"
            (Attributes [])
        , success "[\"a\", \"b\"]"
            (Attributes
                [ MetaPattern $ StringLiteralPattern (StringLiteral "a")
                , MetaPattern $ StringLiteralPattern (StringLiteral "b")
                ])
        , FailureWithoutMessage ["", "a", "\"a\"", "[\"a\" \"a\"]"]
        ]


moduleParserTests :: [TestTree]
moduleParserTests =
    parseTree moduleParser
        [ success "module MN sort c{}[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ SentenceSortSentence SentenceSort
                        { sentenceSortName = Id "c"
                        , sentenceSortParameters = []
                        , sentenceSortAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
        , success "module MN sort c{}[] sort c{}[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ SentenceSortSentence SentenceSort
                        { sentenceSortName = Id "c"
                        , sentenceSortParameters = []
                        , sentenceSortAttributes = Attributes []
                        }
                    , SentenceSortSentence SentenceSort
                        { sentenceSortName = Id "c"
                        , sentenceSortParameters = []
                        , sentenceSortAttributes = Attributes []
                        }
                    ]
                , moduleAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                }
        , success "module MN endmodule []"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences = []
                , moduleAttributes = Attributes []
                }
        , FailureWithoutMessage
            [ ""
            , "MN sort c{}[] endmodule [\"a\"]"
            , "module sort c{}[] endmodule [\"a\"]"
            , "module MN sort c{}[] [\"a\"]"
            , "module MN sort c{}[] endmodule"
            ]
        ]

definitionParserTests :: [TestTree]
definitionParserTests =
    parseTree definitionParser
        [ success "[\"a\"] module M sort c{}[] endmodule [\"b\"]"
            Definition
                { definitionAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ SentenceSortSentence SentenceSort
                                { sentenceSortName = Id "c"
                                , sentenceSortParameters = []
                                , sentenceSortAttributes = Attributes []
                                }
                            ]
                        , moduleAttributes =
                            Attributes
                                [MetaPattern $
                                    StringLiteralPattern (StringLiteral "b")]
                        }
                    ]
                }
        , success
            (  "[\"a\"] "
                ++ "module M sort c{}[] endmodule [\"b\"] "
                ++ "module N sort d{}[] endmodule [\"e\"]"
                )
            Definition
                { definitionAttributes =
                    Attributes
                        [MetaPattern $ StringLiteralPattern (StringLiteral "a")]
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ SentenceSortSentence SentenceSort
                                { sentenceSortName = Id "c"
                                , sentenceSortParameters = []
                                , sentenceSortAttributes = Attributes []
                                }
                            ]
                        , moduleAttributes =
                            Attributes
                                [MetaPattern $
                                    StringLiteralPattern (StringLiteral "b")]
                        }
                    , Module
                        { moduleName = ModuleName "N"
                        , moduleSentences =
                            [ SentenceSortSentence SentenceSort
                                { sentenceSortName = Id "d"
                                , sentenceSortParameters = []
                                , sentenceSortAttributes = Attributes []
                                }
                            ]
                        , moduleAttributes =
                            Attributes
                                [MetaPattern $
                                    StringLiteralPattern (StringLiteral "e")]
                        }
                    ]
                }
        , FailureWithoutMessage
            [ ""
            , "[]"
            , "module M sort c{}[] endmodule [\"b\"]"
            ]
        ]

------------------------------------
-- Generic test utilities
------------------------------------

sortVariableSort :: String -> Sort a
sortVariableSort name =
    SortVariableSort (sortVariable name)

sortVariable :: String -> SortVariable a
sortVariable name =
    SortVariable (Id name)

metaSort :: MetaSortType -> Sort Meta
metaSort sortType =
    SortActualSort SortActual
        { sortActualName = Id (show sortType)
        , sortActualSorts = []}
