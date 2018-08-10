module Test.Kore.Parser.Parser (test_koreParser) where

import Test.Tasty
       ( TestTree, testGroup )

import Kore.AST.Builders
       ( sort_ )
import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureToKore
       (patternPureToKore)
import Kore.AST.Sentence
import Kore.ASTUtils.SmartPatterns
import Kore.Implicit.ImplicitSorts
import Kore.Parser.ParserImpl

import Test.Kore
import Test.Kore.Parser

test_koreParser :: [TestTree]
test_koreParser =
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
    , testGroup "domainValuePatternParser" domainValuePatternParserTests
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
    , testGroup "sentenceHookedSortParser" sentenceHookedSortParserTests
    , testGroup "sentenceHookedSymbolParser" sentenceHookedSymbolParserTests
    , testGroup "moduleParser" moduleParserTests
    , testGroup "definitionParser" definitionParserTests
    ]

objectSortParserTests :: [TestTree]
objectSortParserTests =
    parseTree (sortParser Object)
        [ success "var" $
            SortVariableSort ( SortVariable (testId "var") )
        , success "sort1{}" $
            SortActualSort SortActual
                { sortActualName = testId "sort1"
                , sortActualSorts = []
                }
        , success "sort1{sort2}" $
            SortActualSort SortActual
                { sortActualName = testId "sort1"
                , sortActualSorts =
                    [ SortVariableSort ( SortVariable (testId "sort2") ) ]
                }
        , success "sort1{sort2, sort3}" $
            SortActualSort SortActual
                { sortActualName = testId "sort1"
                , sortActualSorts =
                    [ SortVariableSort ( SortVariable (testId "sort2") )
                    , SortVariableSort ( SortVariable (testId "sort3") )
                    ]
                }
        , success "sort1{sort2{sort3}}" $
            SortActualSort SortActual
                { sortActualName = testId "sort1"
                , sortActualSorts =
                    [ SortActualSort SortActual
                        { sortActualName = testId "sort2"
                        , sortActualSorts =
                            [ SortVariableSort (SortVariable (testId "sort3")) ]
                        }
                    ]
                }
        , FailureWithoutMessage ["var1, var2", "var1{var1 var2}"]
        ]

metaSortConverterTests :: [TestTree]
metaSortConverterTests =
    parseTree (sortParser Meta)
        [ success "#var"
            (SortVariableSort (SortVariable (testId "#var")))
        , success "#Char{}" charMetaSort
        , success "#CharList{}" charListMetaSort
        , success "#Pattern{}" patternMetaSort
        , success "#PatternList{}" patternListMetaSort
        , success "#Sort{}" sortMetaSort
        , success "#SortList{}" sortListMetaSort
        , success "#String{}" charListMetaSort
        , success "#Symbol{}" symbolMetaSort
        , success "#SymbolList{}" symbolListMetaSort
        , success "#Variable{}" variableMetaSort
        , success "#VariableList{}" variableListMetaSort
        , success "#User{}" (sort_ $ MetaBasicSortType $ UserSort "User")
        , FailureWithoutMessage
            [ "var1, var2", "var1{var1 var2}"
            , "sort1{sort2, sort3}", "sort1{sort2{sort3}}"
            ]
        ]

objectSortListParserTests :: [TestTree]
objectSortListParserTests =
    parseTree (inParenthesesListParser (sortParser Object))
        [ success "()" []
        , success "(var)"
            [ sortVariableSort "var" ]
        , success "( var1  , var2   )  "
            [ sortVariableSort "var1"
            , sortVariableSort "var2"
            ]
        , success "(sort1{sort2}, var)"
            [ SortActualSort SortActual
                { sortActualName = testId "sort1"
                , sortActualSorts =
                    [ sortVariableSort "sort2" ]
                }
            , sortVariableSort "var"
            ]
        , FailureWithoutMessage ["(var1 var2)"]
        ]

metaSortListParserTests :: [TestTree]
metaSortListParserTests =
    parseTree (inCurlyBracesListParser (sortParser Meta))
        [ success "{}" []
        , success "{#var}"
            [SortVariableSort (SortVariable (testId "#var"))]
        , success "{#var1, #var2}"
            [ SortVariableSort (SortVariable (testId "#var1"))
            , SortVariableSort (SortVariable (testId "#var2"))
            ]
        , success "{#Char{  }  , #var}"
            [ charMetaSort
            , SortVariableSort (SortVariable (testId "#var"))
            ]
        , FailureWithoutMessage
            [ "{#var1 #var2}", "{#var1, var2}" ]
        ]

objectSortVariableParserTests :: [TestTree]
objectSortVariableParserTests =
    parseTree (sortVariableParser Object)
        [ success "var" (SortVariable (testId "var"))
        , FailureWithoutMessage ["", "#", "#var"]
        ]

metaSortVariableParserTests :: [TestTree]
metaSortVariableParserTests =
    parseTree (sortVariableParser Meta)
        [ success "#var" (SortVariable (testId "#var"))
        , FailureWithoutMessage ["", "#", "var"]
        ]

objectInCurlyBracesSortVariableListParserTest :: [TestTree]
objectInCurlyBracesSortVariableListParserTest =
    parseTree (inCurlyBracesListParser (sortVariableParser Object))
        [ success "{}" []
        , success "{var}"
            [ SortVariable (testId "var") ]
        , success "{var1, var2}"
            [ SortVariable (testId "var1")
            , SortVariable (testId "var2")
            ]
        , FailureWithoutMessage
            [ "{var1 var2}", "{#var1, var2}", "{var, Int{}}" ]
        ]

metaInCurlyBracesSortVariableListParserTest :: [TestTree]
metaInCurlyBracesSortVariableListParserTest =
    parseTree (inCurlyBracesListParser (sortVariableParser Meta))
        [ success "{}" []
        , success "{#var}"
            [ SortVariable (testId "#var") ]
        , success "{#var1, #var2}"
            [ SortVariable (testId "#var1")
            , SortVariable (testId "#var2")
            ]
        , FailureWithoutMessage
            [ "{#var1 #var2}", "{#var1, var2}", "{#var, #Char{}}" ]
        ]

sortVariableParserTests :: [TestTree]
sortVariableParserTests =
    parseTree unifiedSortVariableParser
        [ success "var"
            ( UnifiedObject
                (SortVariable (testId "var"))
            )
        , success "#var"
            ( UnifiedMeta
                (SortVariable (testId "#var"))
            )
        , FailureWithoutMessage ["", "#"]
        ]

objectAliasParserTests :: [TestTree]
objectAliasParserTests =
    parseTree (aliasParser Object)
        [ success "c1{}"
            Alias
                { aliasConstructor = testId "c1"
                , aliasParams = []
                }
        , success "c1{s1}"
            Alias
                { aliasConstructor = testId "c1"
                , aliasParams = [ sortVariable "s1" ]
                }
        , success "c1{s1,s2}"
            Alias
                { aliasConstructor = testId "c1"
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
                { symbolConstructor = testId "c1"
                , symbolParams = []
                }
        , success "c1{s1}"
            Symbol
                { symbolConstructor = testId "c1"
                , symbolParams = [ sortVariable "s1" ]
                }
        , success "c1{s1,s2}"
            Symbol
                { symbolConstructor = testId "c1"
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
                { aliasConstructor = testId "#c1"
                , aliasParams = []
                }
        , success "#c1{#s1}"
            Alias
                { aliasConstructor = testId "#c1"
                , aliasParams = [sortVariable "#s1"]
                }
        , success "#c1{#s1,#s2}"
            Alias
                { aliasConstructor = testId "#c1"
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
                { symbolConstructor = testId "#c1"
                , symbolParams = []
                }
        , success "#c1{#s1}"
            Symbol
                { symbolConstructor = testId "#c1"
                , symbolParams = [sortVariable "#s1"]
                }
        , success "#c1{#s1,#s2}"
            Symbol
                { symbolConstructor = testId "#c1"
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
                { variableName = testId "v"
                , variableSort = sortVariableSort "s"
                }
        , success "v:s1{s2}"
            Variable
                { variableName = testId "v"
                , variableSort =
                    SortActualSort SortActual
                        { sortActualName = testId "s1"
                        , sortActualSorts = [ sortVariableSort "s2" ]
                        }
                }
        , FailureWithoutMessage ["", "var", "v:", ":s"]
        ]

andPatternParserTests :: [TestTree]
andPatternParserTests =
    parseTree korePatternParser
        [ success "\\and{s}(\"a\", \"b\")"
            ( asKorePattern $ AndPattern And
                { andSort = sortVariableSort "s" :: Sort Object
                , andFirst =
                    asKorePattern $ StringLiteralPattern (StringLiteral "a")
                , andSecond =
                    asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "#v:#Char"
            ( asKorePattern $ VariablePattern Variable
                { variableName = testId "#v" :: Id Meta
                , variableSort = sortVariableSort "#Char"
                }
            )
        , success "v:s1{s2}"
            ( asKorePattern $ VariablePattern Variable
                { variableName = testId "v" :: Id Object
                , variableSort =
                    SortActualSort SortActual
                        { sortActualName = testId "s1"
                        , sortActualSorts = [ sortVariableSort "s2" ]
                        }
                }
            )
        , success "c{s1,s2}(v1:s1, v2:s2)"
            ( asKorePattern $ ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId "c" :: Id Object
                        , symbolOrAliasParams =
                            [ sortVariableSort "s1"
                            , sortVariableSort "s2" ]
                        }
                , applicationChildren =
                    [ asKorePattern $ VariablePattern Variable
                        { variableName = testId "v1" :: Id Object
                        , variableSort = sortVariableSort "s1"
                        }
                    , asKorePattern $ VariablePattern Variable
                        { variableName = testId "v2" :: Id Object
                        , variableSort = sortVariableSort "s2"
                        }
                    ]
                }
            )
        , success "c{}()"
            ( asKorePattern $ ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId "c" :: Id Object
                        , symbolOrAliasParams = []
                        }
                , applicationChildren = []
                }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree korePatternParser
        [ success "\\bottom{#Sort}()"
            (asKorePattern $ BottomPattern $ Bottom
                (sortVariableSort "#Sort" :: Sort Meta)
            )
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
    parseTree korePatternParser
        [ success "\\ceil{s1, s2}(\"a\")"
            (asKorePattern $ CeilPattern Ceil
                    { ceilOperandSort = sortVariableSort "s1" :: Sort Object
                    , ceilResultSort = sortVariableSort "s2"
                    , ceilChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
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
domainValuePatternParserTests :: [TestTree]
domainValuePatternParserTests =
    parseTree korePatternParser
        [ success "\\dv{s1}(\"a\")"
            ( patternPureToKore
            $ DV_ (sortVariableSort "s1") (StringLiteral_ (StringLiteral "a"))
            )
        , FailureWithoutMessage
            [ ""
            , "\\dv{s1, s2}(\"a\")"
            , "\\dv{}(\"a\")"
            , "\\dv{s1}()"
            ]
        ]
equalsPatternParserTests :: [TestTree]
equalsPatternParserTests =
    parseTree korePatternParser
        [ success "\\equals{s1, s2}(\"a\", \"b\")"
            ( asKorePattern $ EqualsPattern Equals
                    { equalsOperandSort = sortVariableSort "s1" :: Sort Object
                    , equalsResultSort = sortVariableSort "s2"
                    , equalsFirst =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , equalsSecond =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\exists{#s}(#v:#Char, \"b\")"
            (asKorePattern $ ExistsPattern Exists
                    { existsSort = sortVariableSort "#s" :: Sort Meta
                    , existsVariable =
                        Variable
                            { variableName = testId "#v"
                            , variableSort = sortVariableSort "#Char"
                            }
                    , existsChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\floor{s1, s2}(\"a\")"
            ( asKorePattern $ FloorPattern Floor
                    { floorOperandSort = sortVariableSort "s1" :: Sort Object
                    , floorResultSort = sortVariableSort "s2"
                    , floorChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
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
    parseTree korePatternParser
        [ success "\\forall{s}(v:s1, \"b\")"
            ( asKorePattern $ ForallPattern Forall
                    { forallSort = sortVariableSort "s" :: Sort Object
                    , forallVariable =
                        Variable
                            { variableName = testId "v"
                            , variableSort = sortVariableSort "s1"
                            }
                    , forallChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\iff{s}(\"a\", \"b\")"
            ( asKorePattern $ IffPattern Iff
                    { iffSort = sortVariableSort "s" :: Sort Object
                    , iffFirst =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , iffSecond =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\implies{s}(\"a\", \"b\")"
            ( asKorePattern $ ImpliesPattern Implies
                    { impliesSort = sortVariableSort "s" :: Sort Object
                    , impliesFirst =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , impliesSecond =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\in{s1,s2}(v:s3, \"b\")"
            ( asKorePattern $ InPattern In
                    { inOperandSort = sortVariableSort "s1" :: Sort Object
                    , inResultSort = sortVariableSort "s2"
                    , inContainedChild = asKorePattern $
                        VariablePattern Variable
                            { variableName = testId "v" :: Id Object
                            , variableSort = sortVariableSort "s3"
                            }
                    , inContainingChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , success "\\in{s1,s2}(\"a\", \"b\")"
            ( asKorePattern $ InPattern In
                    { inOperandSort = sortVariableSort "s1" :: Sort Object
                    , inResultSort = sortVariableSort "s2"
                    , inContainedChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , inContainingChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\not{s}(\"a\")"
            ( asKorePattern $ NotPattern Not
                    { notSort = sortVariableSort "s" :: Sort Object
                    , notChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
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
    parseTree korePatternParser
        [ success "\\next{s}(\"a\")"
            ( asKorePattern $ NextPattern Next
                    { nextSort = sortVariableSort "s"
                    , nextChild =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    }
            )
        , Failure FailureTest
            { failureInput = "\\next{#s}(\"a\")"
            , failureExpected =
                "<test-string>:1:7:\n"
                ++"Cannot have a \\next Meta pattern.\n"
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
    parseTree korePatternParser
        [ success "\\or{s}(\"a\", \"b\")"
            ( asKorePattern $ OrPattern Or
                    { orSort = sortVariableSort "s" :: Sort Object
                    , orFirst =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , orSecond =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
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
    parseTree korePatternParser
        [ success "\\rewrites{s}(\"a\", \"b\")"
            ( asKorePattern $ RewritesPattern Rewrites
                    { rewritesSort = sortVariableSort "s"
                    , rewritesFirst =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , rewritesSecond =
                        asKorePattern $ StringLiteralPattern (StringLiteral "b")
                    }
            )
        , Failure FailureTest
            { failureInput = "\\rewrites{#s}(\"a\", \"b\")"
            , failureExpected =
                "<test-string>:1:11:\n"
                ++ "Cannot have a \\rewrites Meta pattern.\n"
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
    parseTree korePatternParser
        [ success "\"hello\""
            (asKorePattern $ StringLiteralPattern (StringLiteral "hello"))
        , success "\"\""
            (asKorePattern $ StringLiteralPattern (StringLiteral ""))
        , success "\"\\\"\""
            (asKorePattern $ StringLiteralPattern (StringLiteral "\""))
        , FailureWithoutMessage ["", "\""]
        ]
topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree korePatternParser
        [ success "\\top{s}()"
            (asKorePattern $ TopPattern $ Top
                (sortVariableSort "s" :: Sort Object)
            )
        , FailureWithoutMessage
            ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"]
        ]
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
    parseTree korePatternParser
        [ success "v:s"
            ( asKorePattern $ VariablePattern Variable
                { variableName = testId "v" :: Id Object
                , variableSort = sortVariableSort "s"
                }
            )
        , success "v:s1{s2}"
            ( asKorePattern $ VariablePattern Variable
                { variableName = testId "v" :: Id Object
                , variableSort = SortActualSort SortActual
                    { sortActualName=testId "s1"
                    , sortActualSorts = [ sortVariableSort "s2" ]
                    }
                }
            )
            , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]

sentenceAliasParserTests :: [TestTree]
sentenceAliasParserTests =
    parseTree koreSentenceParser
        [
          success "alias a{s1}(s2) : s3 where a{s1}(X:s2) := g{}() [\"a\"]"
            ( constructUnifiedSentence SentenceAliasSentence $
                (SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = testId "a"
                        , aliasParams = [ sortVariable "s1" ]
                        }
                    , sentenceAliasSorts = [ sortVariableSort "s2"]
                    , sentenceAliasResultSort = sortVariableSort "s3"
                    , sentenceAliasLeftPattern = ApplicationPattern Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "a" :: Id Object
                                , symbolOrAliasParams = [ sortVariableSort "s1" ]
                                }
                        , applicationChildren =
                            [ asKorePattern $ VariablePattern Variable
                                { variableName = testId "X" :: Id Object
                                , variableSort = sortVariableSort "s2"
                                }
                            ]
                        }
                    , sentenceAliasRightPattern = ApplicationPattern Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "g" :: Id Object
                                , symbolOrAliasParams = [ ]
                                }
                        , applicationChildren = []
                        }
                    , sentenceAliasAttributes =
                        Attributes
                            [asKorePattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
                :: KoreSentenceAlias Object)
            )
        , success "alias a { s1 , s2 } ( s3, s4 ) : s5 where a { s1 , s2 } ( X:s3, Y:s4 ) := b { s1 , s2 } ( X:s3, Y:s4 ) [ \"a\" , \"b\" ]"
            ( constructUnifiedSentence SentenceAliasSentence $
                (SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = testId "a"
                        , aliasParams =
                            [ sortVariable "s1"
                            , sortVariable "s2"
                            ]
                        }
                    , sentenceAliasSorts =
                        [ sortVariableSort "s3"
                        , sortVariableSort "s4"
                        ]
                    , sentenceAliasResultSort = sortVariableSort "s5"
                    , sentenceAliasLeftPattern = ApplicationPattern Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "a" :: Id Object
                                , symbolOrAliasParams =
                                    [
                                          sortVariableSort "s1"
                                        , sortVariableSort "s2"
                                    ]
                                }
                        , applicationChildren =
                            [ asKorePattern $ VariablePattern Variable
                                { variableName = testId "X" :: Id Object
                                , variableSort = sortVariableSort "s3"
                                }
                            , asKorePattern $ VariablePattern Variable
                                { variableName = testId "Y" :: Id Object
                                , variableSort = sortVariableSort "s4"
                                }
                            ]
                        }
                    , sentenceAliasRightPattern = ApplicationPattern Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "b" :: Id Object
                                , symbolOrAliasParams = [ sortVariableSort "s1", sortVariableSort "s2" ]
                                }
                        , applicationChildren =
                            [ asKorePattern $ VariablePattern Variable
                                { variableName = testId "X" :: Id Object
                                , variableSort = sortVariableSort "s3"
                                }
                            , asKorePattern $ VariablePattern Variable
                                { variableName = testId "Y" :: Id Object
                                , variableSort = sortVariableSort "s4"
                                }
                            ]
                        }
                    , sentenceAliasAttributes =
                        Attributes
                            [ asKorePattern $
                                StringLiteralPattern (StringLiteral "a")
                            , asKorePattern $
                                StringLiteralPattern (StringLiteral "b")
                            ]
                    }
                :: KoreSentenceAlias Object)
            )
        , success "alias #a{}() : #Char where #a{}() := #b{}() []"
            ( constructUnifiedSentence SentenceAliasSentence $
                (SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = testId "#a" :: Id Meta
                        , aliasParams = []
                        }
                    , sentenceAliasSorts = []
                    , sentenceAliasResultSort = sortVariableSort "#Char"
                    , sentenceAliasLeftPattern  = ApplicationPattern Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "#a" :: Id Meta
                                , symbolOrAliasParams = [ ]
                                }
                        , applicationChildren = []
                        }
                    , sentenceAliasRightPattern = ApplicationPattern Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "#b" :: Id Meta
                                , symbolOrAliasParams = [ ]
                                }
                        , applicationChildren = []
                        }
                    , sentenceAliasAttributes = Attributes []
                    }
                :: KoreSentenceAlias Meta)
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
    parseTree koreSentenceParser
        [ success "axiom{sv1}\"a\"[\"b\"]"
            ( constructUnifiedSentence SentenceAxiomSentence $
                (SentenceAxiom
                    { sentenceAxiomParameters =
                        [UnifiedObject
                            (SortVariable (testId "sv1"))]
                    , sentenceAxiomPattern =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ asKorePattern
                              $ StringLiteralPattern (StringLiteral "b")
                            ]
                    }
                :: KoreSentenceAxiom)
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , success "axiom{}\"a\"[\"b\"]"
            ( constructUnifiedSentence SentenceAxiomSentence $
                (SentenceAxiom
                    { sentenceAxiomParameters = [] :: [UnifiedSortVariable]
                    , sentenceAxiomPattern =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ asKorePattern
                              $ StringLiteralPattern (StringLiteral "b")
                            ]
                    }
                :: KoreSentenceAxiom)
            )
        , success "axiom { sv1 , sv2 } \"a\" [ \"b\" ] "
            ( constructUnifiedSentence SentenceAxiomSentence $
                (SentenceAxiom
                    { sentenceAxiomParameters =
                        [ UnifiedObject
                            (SortVariable (testId "sv1"))
                        , UnifiedObject
                            (SortVariable (testId "sv2"))
                        ]
                    , sentenceAxiomPattern =
                        asKorePattern $ StringLiteralPattern (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ asKorePattern
                              $ StringLiteralPattern (StringLiteral "b")
                            ]
                    }
                :: KoreSentenceAxiom)
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
    parseTree koreSentenceParser
        [ success "import M[\"b\"]"
            ( constructUnifiedSentence SentenceImportSentence $
                (SentenceImport
                    { sentenceImportModuleName = ModuleName "M"
                    , sentenceImportAttributes =
                        Attributes
                            [ asKorePattern
                              $ StringLiteralPattern (StringLiteral "b")
                            ]
                    }
                :: KoreSentenceImport)
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
    parseTree koreSentenceParser
        [ success "sort s1 { sv1 } [ \"a\" ]"
            ( constructUnifiedSentence SentenceSortSentence $
                (SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = [ sortVariable "sv1" ]
                    , sentenceSortAttributes =
                        Attributes
                            [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                    }
                :: KoreSentenceSort Object)
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , success "sort s1 {} [ \"a\" ]"
            ( constructUnifiedSentence SentenceSortSentence $
                (SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes =
                        Attributes
                            [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                    }
                :: KoreSentenceSort Object)
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
    parseTree koreSentenceParser
        [ success "symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( constructUnifiedSentence SentenceSymbolSentence $
                (SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = testId "sy1"
                        , symbolParams = [ sortVariable "s1" ]
                        }
                    , sentenceSymbolSorts = [ sortVariableSort "s1" ]
                    , sentenceSymbolResultSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes =
                        Attributes
                            [asKorePattern $
                                StringLiteralPattern (StringLiteral "a")]
                    }
                :: KoreSentenceSymbol Object)
            )
        , success "symbol sy1 {} () : s1 [] "
            ( constructUnifiedSentence SentenceSymbolSentence $
                (SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = testId "sy1"
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes = Attributes []
                    }
                :: KoreSentenceSymbol Object)
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

sentenceHookedSortParserTests :: [TestTree]
sentenceHookedSortParserTests =
    parseTree koreSentenceParser
        [ success "hooked-sort s1 { sv1 } [ \"a\" ]"
            ( constructUnifiedSentence SentenceHookSentence $
                (SentenceHookedSort
                    SentenceSort
                        { sentenceSortName = testId "s1"
                        , sentenceSortParameters = [ sortVariable "sv1" ]
                        , sentenceSortAttributes =
                            Attributes
                                [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                        }

                :: KoreSentenceHook)
            )
        {- TODO(virgil): The Scala parser allows empty sort variable lists
           while the semantics-of-k document does not. -}
        , success "hooked-sort s1 {} [ \"a\" ]"
            ( constructUnifiedSentence SentenceHookSentence $
                (SentenceHookedSort
                    SentenceSort
                        { sentenceSortName = testId "s1"
                        , sentenceSortParameters = []
                        , sentenceSortAttributes =
                            Attributes
                                [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                        }
                :: KoreSentenceHook)
            )
        , FailureWithoutMessage
            [ ""
            , "s1 { sv1 } [ \"a\" ]"
            , "hooked-sort { sv1 } [ \"a\" ]"
            , "hooked-sort s1 { sv1{} } [ \"a\" ]"
            , "hooked-sort s1 [ \"a\" ]"
            , "hooked-sort s1 { sv1 } "
            , "hooked-sort { sv1 } s1 [ \"a\" ]"
            ]
        ]

sentenceHookedSymbolParserTests :: [TestTree]
sentenceHookedSymbolParserTests =
    parseTree koreSentenceParser
        [ success "hooked-symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( constructUnifiedSentence SentenceHookSentence $
                (SentenceHookedSymbol
                    SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = testId "sy1"
                            , symbolParams = [ sortVariable "s1" ]
                            }
                        , sentenceSymbolSorts = [ sortVariableSort "s1" ]
                        , sentenceSymbolResultSort = sortVariableSort "s1"
                        , sentenceSymbolAttributes =
                            Attributes
                                [asKorePattern $
                                    StringLiteralPattern (StringLiteral "a")]
                        }
                :: KoreSentenceHook)
            )
        , success "hooked-symbol sy1 {} () : s1 [] "
            ( constructUnifiedSentence SentenceHookSentence $
                (SentenceHookedSymbol
                    SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = testId "sy1"
                            , symbolParams = []
                            }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort = sortVariableSort "s1"
                        , sentenceSymbolAttributes = Attributes []
                        }
                :: KoreSentenceHook)
            )
        , FailureWithoutMessage
            [ ""
            , "sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            , "hooked-symbol { s1 } ( s1 ) : s1 [\"a\"] "
            , "hooked-symbol sy1 ( s1 ) : s1 [\"a\"] "
            , "hooked-symbol sy1 { s1 } : s1 [\"a\"] "
            , "hooked-symbol sy1 { s1 } ( s1 ) s1 [\"a\"] "
            , "hooked-symbol sy1 { s1 } ( s1 ) : [\"a\"] "
            , "hooked-symbol sy1 { s1 } ( s1 ) : s1 "
            , "hooked-symbol sy1 { s1 } ( s1 ) [\"a\"] "
            ]
        ]

attributesParserTests :: [TestTree]
attributesParserTests =
    parseTree attributesParser
        [ success "[\"a\"]"
            (Attributes
                [asKorePattern $ StringLiteralPattern (StringLiteral "a")])
        , success "[]" (Attributes [])
        , success "[\"a\", \"b\"]"
            (Attributes
                [ asKorePattern $ StringLiteralPattern (StringLiteral "a")
                , asKorePattern $ StringLiteralPattern (StringLiteral "b")
                ])
        , FailureWithoutMessage ["", "a", "\"a\"", "[\"a\" \"a\"]"]
        ]


moduleParserTests :: [TestTree]
moduleParserTests =
    parseTree (moduleParser koreSentenceParser)
        [ success "module MN sort c{}[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ asSentence
                        (SentenceSort
                            { sentenceSortName = testId "c"
                            , sentenceSortParameters = []
                            , sentenceSortAttributes = Attributes []
                            }
                        :: KoreSentenceSort Object)
                    ]
                , moduleAttributes =
                    Attributes
                        [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                }
        , success "module MN sort c{}[] sort c{}[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ constructUnifiedSentence SentenceSortSentence $
                        (SentenceSort
                            { sentenceSortName = testId "c"
                            , sentenceSortParameters = []
                            , sentenceSortAttributes = Attributes []
                            }
                        :: KoreSentenceSort Object)
                    , constructUnifiedSentence SentenceSortSentence $
                        (SentenceSort
                            { sentenceSortName = testId "c"
                            , sentenceSortParameters = []
                            , sentenceSortAttributes = Attributes []
                            }
                        :: KoreSentenceSort Object)
                    ]
                , moduleAttributes =
                    Attributes
                        [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
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
    parseTree (definitionParser koreSentenceParser)
        [ success "[\"a\"] module M sort c{}[] endmodule [\"b\"]"
            Definition
                { definitionAttributes =
                    Attributes
                        [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ asSentence
                                (SentenceSort
                                    { sentenceSortName = testId "c"
                                    , sentenceSortParameters = []
                                    , sentenceSortAttributes = Attributes []
                                    }
                                :: KoreSentenceSort Object)
                            ]
                        , moduleAttributes =
                            Attributes
                                [asKorePattern $
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
                        [asKorePattern $ StringLiteralPattern (StringLiteral "a")]
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ asSentence
                                (SentenceSort
                                    { sentenceSortName = testId "c"
                                    , sentenceSortParameters = []
                                    , sentenceSortAttributes = Attributes []
                                    }
                                :: KoreSentenceSort Object)
                            ]
                        , moduleAttributes =
                            Attributes
                                [asKorePattern $
                                    StringLiteralPattern (StringLiteral "b")]
                        }
                    , Module
                        { moduleName = ModuleName "N"
                        , moduleSentences =
                            [ asSentence
                                (SentenceSort
                                    { sentenceSortName = testId "d"
                                    , sentenceSortParameters = []
                                    , sentenceSortAttributes = Attributes []
                                    }
                                :: KoreSentenceSort Object)
                            ]
                        , moduleAttributes =
                            Attributes
                                [asKorePattern $
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
    SortVariable (testId name)
