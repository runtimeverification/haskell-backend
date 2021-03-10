module Test.Kore.Parser.Parser (
    test_koreParser,
    test_parseSortVariable,
    test_parseSort,
) where

import Prelude.Kore

import Test.Tasty (
    TestTree,
    testGroup,
 )

import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Data.Text (
    Text,
    pack,
 )

import Data.Sup
import qualified Kore.Builtin as Builtin
import qualified Kore.Internal.TermLike as Internal
import Kore.Parser.Lexer
import Kore.Parser.Parser
import Kore.Syntax
import Kore.Syntax.Definition

import Test.Kore hiding (
    sortVariable,
    sortVariableSort,
 )
import Test.Kore.Parser

test_koreParser :: [TestTree]
test_koreParser =
    [ testGroup "objectSortParser" objectSortParserTests
    , testGroup "objectSortVariableParser" objectSortVariableParserTests
    , testGroup "objectAliasParser" objectAliasParserTests
    , testGroup "objectSymbolParser" objectSymbolParserTests
    , testGroup "variableParser" variableParserTests
    , testGroup "setVariableParser" setVariableParserTests
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
    , testGroup "muPatternParser" muPatternParserTests
    , testGroup "nextPatternParser" nextPatternParserTests
    , testGroup "notPatternParser" notPatternParserTests
    , testGroup "nuPatternParser" nuPatternParserTests
    , testGroup "orPatternParser" orPatternParserTests
    , testGroup "rewritesPatternParser" rewritesPatternParserTests
    , testGroup "stringLiteralPatternParser" stringLiteralPatternParserTests
    , testGroup "topPatternParser" topPatternParserTests
    , testGroup "variablePatternParser" variablePatternParserTests
    , testGroup "sentenceAliasParser" sentenceAliasParserTests
    , testGroup "sentenceImportParser" sentenceImportParserTests
    , testGroup "sentenceAxiomParser" sentenceAxiomParserTests
    , testGroup "sentenceClaimParser" sentenceClaimParserTests
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
    parseTree
        parseSort
        [ success "var" $
            SortVariableSort (SortVariable (testId "var"))
        , success "sort1{}" $
            SortActualSort
                SortActual
                    { sortActualName = testId "sort1"
                    , sortActualSorts = []
                    }
        , success "sort1{sort2}" $
            SortActualSort
                SortActual
                    { sortActualName = testId "sort1"
                    , sortActualSorts =
                        [SortVariableSort (SortVariable (testId "sort2"))]
                    }
        , success "sort1{sort2, sort3}" $
            SortActualSort
                SortActual
                    { sortActualName = testId "sort1"
                    , sortActualSorts =
                        [ SortVariableSort (SortVariable (testId "sort2"))
                        , SortVariableSort (SortVariable (testId "sort3"))
                        ]
                    }
        , success "sort1{sort2{sort3}}" $
            SortActualSort
                SortActual
                    { sortActualName = testId "sort1"
                    , sortActualSorts =
                        [ SortActualSort
                            SortActual
                                { sortActualName = testId "sort2"
                                , sortActualSorts =
                                    [SortVariableSort (SortVariable (testId "sort3"))]
                                }
                        ]
                    }
        , FailureWithoutMessage ["var1, var2", "var1{var1 var2}"]
        ]

test_parseSort :: [TestTree]
test_parseSort =
    parseTree
        (parens . list $ parseSort)
        [ success "()" []
        , success
            "(var)"
            [sortVariableSort "var"]
        , success
            "( var1  , var2   )  "
            [ sortVariableSort "var1"
            , sortVariableSort "var2"
            ]
        , success
            "(sort1{sort2}, var)"
            [ SortActualSort
                SortActual
                    { sortActualName = testId "sort1"
                    , sortActualSorts =
                        [sortVariableSort "sort2"]
                    }
            , sortVariableSort "var"
            ]
        , FailureWithoutMessage ["(var1 var2)"]
        ]

objectSortVariableParserTests :: [TestTree]
objectSortVariableParserTests =
    parseTree
        parseSortVariable
        [ success "var" (SortVariable (testId "var"))
        , FailureWithoutMessage ["", "#"]
        ]

test_parseSortVariable :: [TestTree]
test_parseSortVariable =
    parseTree
        (braces . list $ parseSortVariable)
        [ success "{}" []
        , success
            "{var}"
            [SortVariable (testId "var")]
        , success
            "{var1, var2}"
            [ SortVariable (testId "var1")
            , SortVariable (testId "var2")
            ]
        , FailureWithoutMessage
            ["{var1 var2}", "{var, Int{}}", "{var, #Char{}}"]
        ]

objectAliasParserTests :: [TestTree]
objectAliasParserTests =
    parseTree
        parseAliasHead
        [ success
            "c1{}"
            Alias
                { aliasConstructor = testId "c1"
                , aliasParams = []
                }
        , success
            "c1{s1}"
            Alias
                { aliasConstructor = testId "c1"
                , aliasParams = [sortVariable "s1"]
                }
        , success
            "c1{s1,s2}"
            Alias
                { aliasConstructor = testId "c1"
                , aliasParams =
                    [ sortVariable "s1"
                    , sortVariable "s2"
                    ]
                }
        , FailureWithoutMessage
            [ "alias"
            , "a1{a2},a1{a2}"
            , "a1{a2 a2}"
            , "a1{a2}a1{a2}"
            , "c1{s1{}}"
            , "c1{#Char{}}"
            ]
        ]

objectSymbolParserTests :: [TestTree]
objectSymbolParserTests =
    parseTree
        parseSymbolHead
        [ success
            "c1{}"
            Symbol
                { symbolConstructor = testId "c1"
                , symbolParams = []
                }
        , success
            "c1{s1}"
            Symbol
                { symbolConstructor = testId "c1"
                , symbolParams = [sortVariable "s1"]
                }
        , success
            "c1{s1,s2}"
            Symbol
                { symbolConstructor = testId "c1"
                , symbolParams =
                    [ sortVariable "s1"
                    , sortVariable "s2"
                    ]
                }
        , FailureWithoutMessage
            [ "symbol"
            , "a1{a2},a1{a2}"
            , "a1{a2 a2}"
            , "a1{a2}a1{a2}"
            , "c1{s1{}}"
            , "c1{#Char{}}"
            ]
        ]

variableParserTests :: [TestTree]
variableParserTests =
    parseTree
        parseElementVariable
        [ success
            "v:s"
            (mkElementVariable (testId "v") (sortVariableSort "s"))
        , success
            "v0:s"
            ( mkElementVariable (testId "v") (sortVariableSort "s")
                & Lens.set
                    (Lens.mapped . Lens.mapped . field @"counter")
                    (Just (Element 0))
            )
        , success
            "v1:s"
            ( mkElementVariable (testId "v") (sortVariableSort "s")
                & Lens.set
                    (Lens.mapped . Lens.mapped . field @"counter")
                    (Just (Element 1))
            )
        , success
            "v00:s"
            ( mkElementVariable (testId "v0") (sortVariableSort "s")
                & Lens.set
                    (Lens.mapped . Lens.mapped . field @"counter")
                    (Just (Element 0))
            )
        , success
            "v01:s"
            ( mkElementVariable (testId "v0") (sortVariableSort "s")
                & Lens.set
                    (Lens.mapped . Lens.mapped . field @"counter")
                    (Just (Element 1))
            )
        , success "v:s1{s2}" $
            mkElementVariable (testId "v") $
                SortActualSort
                    SortActual
                        { sortActualName = testId "s1"
                        , sortActualSorts = [sortVariableSort "s2"]
                        }
        , FailureWithoutMessage ["", "var", "v:", ":s", "@v:s"]
        ]

setVariableParserTests :: [TestTree]
setVariableParserTests =
    parseTree
        parseSetVariable
        [ success "@v:s" $ mkSetVariable (testId "@v") (sortVariableSort "s")
        , success "@v:s1{s2}" $
            mkSetVariable (testId "@v") $
                SortActualSort
                    SortActual
                        { sortActualName = testId "s1"
                        , sortActualSorts = [sortVariableSort "s2"]
                        }
        , FailureWithoutMessage ["", "@var", "@v:", ":s", "v:s"]
        ]

andPatternParserTests :: [TestTree]
andPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\and{s}(\"a\", \"b\")"
            ( embedParsedPattern $
                AndF
                    And
                        { andSort = sortVariableSort "s" :: Sort
                        , andFirst =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , andSecond =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
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
    parseTree
        parsePattern
        [ success
            "@v:Char"
            ( embedParsedPattern . VariableF . Const . inject $
                mkSetVariable (testId "@v") (sortVariableSort "Char")
            )
        , success
            "v:s1{s2}"
            ( embedParsedPattern $
                VariableF . Const . inject $
                    mkElementVariable (testId "v") $
                        SortActualSort
                            SortActual
                                { sortActualName = testId "s1"
                                , sortActualSorts = [sortVariableSort "s2"]
                                }
            )
        , success
            "c{s1,s2}(v1:s1, v2:s2)"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "c" :: Id
                                , symbolOrAliasParams =
                                    [ sortVariableSort "s1"
                                    , sortVariableSort "s2"
                                    ]
                                }
                        , applicationChildren =
                            [ mkElementVariable (testId "v") (sortVariableSort "s1")
                                & Lens.set
                                    (Lens.mapped . Lens.mapped . field @"counter")
                                    (Just (Element 1))
                                & inject
                                & Const
                                & VariableF
                                & embedParsedPattern
                            , mkElementVariable (testId "v") (sortVariableSort "s2")
                                & Lens.set
                                    (Lens.mapped . Lens.mapped . field @"counter")
                                    (Just (Element 2))
                                & inject
                                & Const
                                & VariableF
                                & embedParsedPattern
                            ]
                        }
            )
        , success
            "c{}()"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "c" :: Id
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren = []
                        }
            )
        , success
            "\\mem{s1, s2}(v:s3, \"b\")"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "\\mem"
                                , symbolOrAliasParams =
                                    [ sortVariableSort "s1"
                                    , sortVariableSort "s2"
                                    ]
                                }
                        , applicationChildren =
                            [ mkElementVariable (testId "v") (sortVariableSort "s3")
                                & inject
                                & Const
                                & VariableF
                                & embedParsedPattern
                            , StringLiteral "b"
                                & Const
                                & StringLiteralF
                                & embedParsedPattern
                            ]
                        }
            )
        , success
            "\\left-assoc{}(c{}(\"a\"))"
            ( StringLiteral "a"
                & Const
                & StringLiteralF
                & embedParsedPattern
            )
        , success
            "\\left-assoc{}(c{}(\"a\", \"b\"))"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "c"
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren =
                            map
                                embedParsedPattern
                                [ StringLiteral "a"
                                    & Const
                                    & StringLiteralF
                                , StringLiteral "b"
                                    & Const
                                    & StringLiteralF
                                ]
                        }
            )
        , success
            "\\left-assoc{}(c{}(\"a\", \"b\", \"c\"))"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "c"
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren =
                            map
                                embedParsedPattern
                                [ ApplicationF
                                    Application
                                        { applicationSymbolOrAlias =
                                            SymbolOrAlias
                                                { symbolOrAliasConstructor = testId "c"
                                                , symbolOrAliasParams = []
                                                }
                                        , applicationChildren =
                                            map
                                                embedParsedPattern
                                                [ StringLiteral "a" & Const & StringLiteralF
                                                , StringLiteral "b" & Const & StringLiteralF
                                                ]
                                        }
                                , StringLiteral "c" & Const & StringLiteralF
                                ]
                        }
            )
        , success
            "\\right-assoc{}(c{}(\"a\"))"
            ( StringLiteral "a"
                & Const
                & StringLiteralF
                & embedParsedPattern
            )
        , success
            "\\right-assoc{}(c{}(\"a\", \"b\"))"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "c"
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren =
                            map
                                embedParsedPattern
                                [ StringLiteral "a" & Const & StringLiteralF
                                , StringLiteral "b" & Const & StringLiteralF
                                ]
                        }
            )
        , success
            "\\right-assoc{}(c{}(\"a\", \"b\", \"c\"))"
            ( embedParsedPattern $
                ApplicationF
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "c"
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren =
                            map
                                embedParsedPattern
                                [ StringLiteral "a" & Const & StringLiteralF
                                , ApplicationF
                                    Application
                                        { applicationSymbolOrAlias =
                                            SymbolOrAlias
                                                { symbolOrAliasConstructor = testId "c"
                                                , symbolOrAliasParams = []
                                                }
                                        , applicationChildren =
                                            map
                                                embedParsedPattern
                                                [ StringLiteral "b" & Const & StringLiteralF
                                                , StringLiteral "c" & Const & StringLiteralF
                                                ]
                                        }
                                ]
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "var"
            , "v:"
            , ":s"
            , "c(s)"
            , "c{s}"
            , "\\left-assoc{}(c{}())"
            , "\\right-assoc{}(c{}())"
            ]
        ]
bottomPatternParserTests :: [TestTree]
bottomPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\bottom{Sort}()"
            ( embedParsedPattern $
                BottomF $
                    Bottom
                        (sortVariableSort "Sort" :: Sort)
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
    parseTree
        parsePattern
        [ success
            "\\ceil{s1, s2}(\"a\")"
            ( embedParsedPattern $
                CeilF
                    Ceil
                        { ceilOperandSort = sortVariableSort "s1" :: Sort
                        , ceilResultSort = sortVariableSort "s2"
                        , ceilChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
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
    parseTree
        parsePattern
        [ success "\\dv{s1}(\"a\")" $
            Builtin.externalize $
                Internal.mkDomainValue
                    DomainValue
                        { domainValueSort = sortVariableSort "s1"
                        , domainValueChild = Internal.mkStringLiteral "a"
                        }
        , FailureWithoutMessage
            [ ""
            , "\\dv{s1, s2}(\"a\")"
            , "\\dv{}(\"a\")"
            , "\\dv{s1}()"
            ]
        ]
equalsPatternParserTests :: [TestTree]
equalsPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\equals{s1, s2}(\"a\", \"b\")"
            ( embedParsedPattern $
                EqualsF
                    Equals
                        { equalsOperandSort = sortVariableSort "s1" :: Sort
                        , equalsResultSort = sortVariableSort "s2"
                        , equalsFirst =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , equalsSecond =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
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
    parseTree
        parsePattern
        [ success
            "\\exists{s}(v:Char, \"b\")"
            ( embedParsedPattern $
                ExistsF
                    Exists
                        { existsSort = sortVariableSort "s" :: Sort
                        , existsVariable =
                            mkElementVariable (testId "v") (sortVariableSort "Char")
                        , existsChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
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
            , "\\exists{s}(@v:s, \"b\")"
            ]
        ]
floorPatternParserTests :: [TestTree]
floorPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\floor{s1, s2}(\"a\")"
            ( embedParsedPattern $
                FloorF
                    Floor
                        { floorOperandSort = sortVariableSort "s1" :: Sort
                        , floorResultSort = sortVariableSort "s2"
                        , floorChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
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
    parseTree
        parsePattern
        [ success
            "\\forall{s}(v:s1, \"b\")"
            ( embedParsedPattern $
                ForallF
                    Forall
                        { forallSort = sortVariableSort "s" :: Sort
                        , forallVariable =
                            mkElementVariable (testId "v") (sortVariableSort "s1")
                        , forallChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
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
    parseTree
        parsePattern
        [ success
            "\\iff{s}(\"a\", \"b\")"
            ( embedParsedPattern $
                IffF
                    Iff
                        { iffSort = sortVariableSort "s" :: Sort
                        , iffFirst =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , iffSecond =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "\\iff{s,s}(\"a\", \"b\")"
            , "\\iff{}(\"a\", \"b\")"
            , "\\iff{s}(\"a\")"
            , "\\iff{s}(\"a\", \"b\", \"c\")"
            , "\\iff{s}(\"a\" \"b\")"
            ]
        ]
impliesPatternParserTests :: [TestTree]
impliesPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\implies{s}(\"a\", \"b\")"
            ( embedParsedPattern $
                ImpliesF
                    Implies
                        { impliesSort = sortVariableSort "s" :: Sort
                        , impliesFirst =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , impliesSecond =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "\\implies{s,s}(\"a\", \"b\")"
            , "\\implies{}(\"a\", \"b\")"
            , "\\implies{s}(\"a\")"
            , "\\implies{s}(\"a\", \"b\", \"c\")"
            , "\\implies{s}(\"a\" \"b\")"
            ]
        ]
memPatternParserTests :: [TestTree]
memPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\in{s1,s2}(v:s3, \"b\")"
            ( embedParsedPattern $
                InF
                    In
                        { inOperandSort = sortVariableSort "s1" :: Sort
                        , inResultSort = sortVariableSort "s2"
                        , inContainedChild =
                            embedParsedPattern $
                                VariableF $
                                    Const $
                                        inject $
                                            mkElementVariable (testId "v") (sortVariableSort "s3")
                        , inContainingChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                        }
            )
        , success
            "\\in{s1,s2}(\"a\", \"b\")"
            ( embedParsedPattern $
                InF
                    In
                        { inOperandSort = sortVariableSort "s1" :: Sort
                        , inResultSort = sortVariableSort "s2"
                        , inContainedChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , inContainingChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                        }
            )
        , FailureWithoutMessage
            [ ""
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
muPatternParserTests :: [TestTree]
muPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\mu{}(@v:s, \\top{s}())"
            ( embedParsedPattern $
                MuF
                    Mu
                        { muVariable =
                            mkSetVariable (testId "@v") (sortVariableSort "s")
                        , muChild =
                            embedParsedPattern $ TopF (Top (sortVariableSort "s"))
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "\\mu{}(v:s, \\top{s}())"
            , "\\mu{}(v:s1, \"b\")"
            , "\\mu{s,s}(v:s1, \"b\")"
            , "\\mu{s}(\"b\", \"b\")"
            , "\\mu{s}(, \"b\")"
            , "\\mu{s}(\"b\")"
            , "\\mu{s}(v:s1, )"
            , "\\mu{s}(v:s1)"
            , "\\mu{s}()"
            , "\\mu{s}"
            , "\\mu"
            , "\\mu(v:s1, \"b\")"
            , "\\mu{s}(@v:s, \"b\")"
            ]
        ]
notPatternParserTests :: [TestTree]
notPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\not{s}(\"a\")"
            ( embedParsedPattern $
                NotF
                    Not
                        { notSort = sortVariableSort "s" :: Sort
                        , notChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
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
    parseTree
        parsePattern
        [ success
            "\\next{s}(\"a\")"
            ( embedParsedPattern $
                NextF
                    Next
                        { nextSort = sortVariableSort "s"
                        , nextChild =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        }
            )
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
nuPatternParserTests :: [TestTree]
nuPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\nu{}(@v:s, \\top{s}())"
            ( embedParsedPattern $
                NuF
                    Nu
                        { nuVariable =
                            mkSetVariable (testId "@v") (sortVariableSort "s")
                        , nuChild =
                            embedParsedPattern $ TopF (Top (sortVariableSort "s"))
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "\\nu{}(v:s, \\top{s}())"
            , "\\nu{}(v:s1, \"b\")"
            , "\\nu{s,s}(v:s1, \"b\")"
            , "\\nu{s}(\"b\", \"b\")"
            , "\\nu{s}(, \"b\")"
            , "\\nu{s}(\"b\")"
            , "\\nu{s}(v:s1, )"
            , "\\nu{s}(v:s1)"
            , "\\nu{s}()"
            , "\\nu{s}"
            , "\\nu"
            , "\\nu(v:s1, \"b\")"
            , "\\nu{s}(@v:s, \"b\")"
            ]
        ]
orPatternParserTests :: [TestTree]
orPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\or{s}(\"a\", \"b\")"
            ( embedParsedPattern $
                OrF
                    Or
                        { orSort = sortVariableSort "s" :: Sort
                        , orFirst =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , orSecond =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "\\or{s,s}(\"a\", \"b\")"
            , "\\or{}(\"a\", \"b\")"
            , "\\or{s}(\"a\")"
            , "\\or{s}(\"a\", \"b\", \"c\")"
            , "\\or{s}(\"a\" \"b\")"
            ]
        ]
rewritesPatternParserTests :: [TestTree]
rewritesPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\rewrites{s}(\"a\", \"b\")"
            ( embedParsedPattern $
                RewritesF
                    Rewrites
                        { rewritesSort = sortVariableSort "s"
                        , rewritesFirst =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                        , rewritesSecond =
                            embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                        }
            )
        , FailureWithoutMessage
            [ ""
            , "\\rewrites{s,s}(\"a\", \"b\")"
            , "\\rewrites{}(\"a\", \"b\")"
            , "\\rewrites{s}(\"a\")"
            , "\\rewrites{s}(\"a\", \"b\", \"c\")"
            , "\\rewrites{s}(\"a\" \"b\")"
            ]
        ]
stringLiteralPatternParserTests :: [TestTree]
stringLiteralPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\"hello\""
            (embedParsedPattern $ StringLiteralF $ Const (StringLiteral "hello"))
        , success
            "\"\""
            (embedParsedPattern $ StringLiteralF $ Const (StringLiteral ""))
        , success
            "\"\\\"\""
            (embedParsedPattern $ StringLiteralF $ Const (StringLiteral "\""))
        , FailureWithoutMessage ["", "\""]
        ]
topPatternParserTests :: [TestTree]
topPatternParserTests =
    parseTree
        parsePattern
        [ success
            "\\top{s}()"
            ( embedParsedPattern $
                TopF $
                    Top
                        (sortVariableSort "s" :: Sort)
            )
        , FailureWithoutMessage
            ["", "\\top()", "\\top{}()", "\\top{s, s}()", "\\top{s}"]
        ]
variablePatternParserTests :: [TestTree]
variablePatternParserTests =
    parseTree
        parsePattern
        [ success
            "v:s"
            ( embedParsedPattern $
                VariableF $
                    Const $
                        inject $
                            mkElementVariable (testId "v") (sortVariableSort "s")
            )
        , success
            "v:s1{s2}"
            ( embedParsedPattern $
                VariableF $
                    Const $
                        inject $
                            mkElementVariable (testId "v") $
                                SortActualSort
                                    SortActual
                                        { sortActualName = testId "s1"
                                        , sortActualSorts = [sortVariableSort "s2"]
                                        }
            )
        , FailureWithoutMessage ["", "var", "v:", ":s", "c(s)", "c{s}"]
        ]

sentenceAliasParserTests :: [TestTree]
sentenceAliasParserTests =
    parseTree
        parseSentence
        [ success
            "alias a{s1}(s2) : s3 where a{s1}(X:s2) := g{}() [\"a\"]"
            ( SentenceAliasSentence
                ( SentenceAlias
                    { sentenceAliasAlias =
                        Alias
                            { aliasConstructor = testId "a"
                            , aliasParams = [sortVariable "s1"]
                            }
                    , sentenceAliasSorts = [sortVariableSort "s2"]
                    , sentenceAliasResultSort = sortVariableSort "s3"
                    , sentenceAliasLeftPattern =
                        Application
                            { applicationSymbolOrAlias =
                                SymbolOrAlias
                                    { symbolOrAliasConstructor = testId "a" :: Id
                                    , symbolOrAliasParams =
                                        [sortVariableSort "s1"]
                                    }
                            , applicationChildren =
                                [ inject $
                                    mkElementVariable
                                        (testId "X")
                                        (sortVariableSort "s2")
                                ]
                            }
                    , sentenceAliasRightPattern =
                        embedParsedPattern $
                            ApplicationF
                                Application
                                    { applicationSymbolOrAlias =
                                        SymbolOrAlias
                                            { symbolOrAliasConstructor = testId "g"
                                            , symbolOrAliasParams = []
                                            }
                                    , applicationChildren = []
                                    }
                    , sentenceAliasAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "a")
                            ]
                    } ::
                    ParsedSentenceAlias
                )
            )
        , success
            "alias a { s1 , s2 } ( s3, s4 ) : s5 where a { s1 , s2 } ( X:s3, Y:s4 ) := b { s1 , s2 } ( X:s3, Y:s4 ) [ \"a\" , \"b\" ]"
            ( SentenceAliasSentence
                ( SentenceAlias
                    { sentenceAliasAlias =
                        Alias
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
                    , sentenceAliasLeftPattern =
                        Application
                            { applicationSymbolOrAlias =
                                SymbolOrAlias
                                    { symbolOrAliasConstructor = testId "a"
                                    , symbolOrAliasParams =
                                        [ sortVariableSort "s1"
                                        , sortVariableSort "s2"
                                        ]
                                    }
                            , applicationChildren =
                                [ inject $
                                    mkElementVariable
                                        (testId "X")
                                        (sortVariableSort "s3")
                                , inject $
                                    mkElementVariable
                                        (testId "Y")
                                        (sortVariableSort "s4")
                                ]
                            }
                    , sentenceAliasRightPattern =
                        embedParsedPattern $
                            ApplicationF
                                Application
                                    { applicationSymbolOrAlias =
                                        SymbolOrAlias
                                            { symbolOrAliasConstructor = testId "b"
                                            , symbolOrAliasParams =
                                                [ sortVariableSort "s1"
                                                , sortVariableSort "s2"
                                                ]
                                            }
                                    , applicationChildren =
                                        [ embedParsedPattern $
                                            VariableF $
                                                Const $
                                                    inject $
                                                        mkElementVariable
                                                            (testId "X")
                                                            (sortVariableSort "s3")
                                        , embedParsedPattern $
                                            VariableF $
                                                Const $
                                                    inject $
                                                        mkElementVariable
                                                            (testId "Y")
                                                            (sortVariableSort "s4")
                                        ]
                                    }
                    , sentenceAliasAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "a")
                            , embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAlias
                )
            )
        , success
            "alias a{}() : Char where a{}() := b{}() []"
            ( SentenceAliasSentence
                ( SentenceAlias
                    { sentenceAliasAlias =
                        Alias
                            { aliasConstructor = testId "a" :: Id
                            , aliasParams = []
                            }
                    , sentenceAliasSorts = []
                    , sentenceAliasResultSort = sortVariableSort "Char"
                    , sentenceAliasLeftPattern =
                        Application
                            { applicationSymbolOrAlias =
                                SymbolOrAlias
                                    { symbolOrAliasConstructor =
                                        testId "a" :: Id
                                    , symbolOrAliasParams = []
                                    }
                            , applicationChildren = []
                            }
                    , sentenceAliasRightPattern =
                        (embedParsedPattern . ApplicationF)
                            Application
                                { applicationSymbolOrAlias =
                                    SymbolOrAlias
                                        { symbolOrAliasConstructor =
                                            testId "b" :: Id
                                        , symbolOrAliasParams = []
                                        }
                                , applicationChildren = []
                                }
                    , sentenceAliasAttributes = Attributes []
                    } ::
                    ParsedSentenceAlias
                )
            )
        , success
            "alias f{s}() : s where f{s}() := \\dv{s}(\"f\") []"
            ( let aliasId :: Id
                  aliasId = testId "f"
                  sortVar = sortVariable "s"
                  resultSort = sortVariableSort "s"
                  aliasHead =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = aliasId
                        , symbolOrAliasParams = [resultSort]
                        }
               in SentenceAliasSentence
                    SentenceAlias
                        { sentenceAliasAlias =
                            Alias
                                { aliasConstructor = aliasId
                                , aliasParams = [sortVar]
                                }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort = sortVariableSort "s"
                        , sentenceAliasLeftPattern =
                            Application
                                { applicationSymbolOrAlias = aliasHead
                                , applicationChildren = []
                                }
                        , sentenceAliasRightPattern =
                            Builtin.externalize $
                                Internal.mkDomainValue
                                    DomainValue
                                        { domainValueSort = resultSort
                                        , domainValueChild = Internal.mkStringLiteral "f"
                                        }
                        , sentenceAliasAttributes = Attributes []
                        }
            )
        , success
            "alias rewrites{s}(s, s) : s \
            \where rewrites{s}(a : s, b : s) := \\rewrites{s}(a : s, b : s) []"
            ( let aliasId :: Id
                  aliasId = testId "rewrites"
                  sortVar = sortVariable "s"
                  resultSort = sortVariableSort "s"
                  aliasHead =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = aliasId
                        , symbolOrAliasParams = [resultSort]
                        }
                  var name = mkElementVariable (testId name) resultSort
                  argument name = Internal.mkElemVar (var name)
                  varA = var "a"
                  varB = var "b"
                  argA = argument "a"
                  argB = argument "b"
               in SentenceAliasSentence
                    SentenceAlias
                        { sentenceAliasAlias =
                            Alias
                                { aliasConstructor = aliasId
                                , aliasParams = [sortVar]
                                }
                        , sentenceAliasSorts = [resultSort, resultSort]
                        , sentenceAliasResultSort = resultSort
                        , sentenceAliasLeftPattern =
                            Application
                                { applicationSymbolOrAlias = aliasHead
                                , applicationChildren = inject <$> [varA, varB]
                                }
                        , sentenceAliasRightPattern =
                            Builtin.externalize $
                                Internal.mkRewrites argA argB
                        , sentenceAliasAttributes = Attributes []
                        }
            )
        , success
            "alias next{s}(s) : s \
            \where next{s}(a : s) := \\next{s}(a : s) []"
            ( let aliasId :: Id
                  aliasId = testId "next"
                  sortVar = sortVariable "s"
                  resultSort = sortVariableSort "s"
                  aliasHead =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = aliasId
                        , symbolOrAliasParams = [resultSort]
                        }
                  var = mkElementVariable (testId "a") resultSort
                  arg = Internal.mkElemVar var
               in SentenceAliasSentence
                    SentenceAlias
                        { sentenceAliasAlias =
                            Alias
                                { aliasConstructor = aliasId
                                , aliasParams = [sortVar]
                                }
                        , sentenceAliasSorts = [resultSort]
                        , sentenceAliasResultSort = resultSort
                        , sentenceAliasLeftPattern =
                            Application
                                { applicationSymbolOrAlias = aliasHead
                                , applicationChildren = [inject var]
                                }
                        , sentenceAliasRightPattern =
                            Builtin.externalize $ Internal.mkNext arg
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
    parseTree
        parseSentence
        [ success
            "axiom{sv1}\"a\"[\"b\"]"
            ( SentenceAxiomSentence
                ( SentenceAxiom
                    { sentenceAxiomParameters =
                        [SortVariable (testId "sv1")]
                    , sentenceAxiomPattern =
                        embedParsedPattern $
                            StringLiteralF $ Const (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAxiom
                )
            )
        , {- TODO(virgil): The Scala parser allows empty sort variable lists
             while the semantics-of-k document does not. -}
          success
            "axiom{}\"a\"[\"b\"]"
            ( SentenceAxiomSentence
                ( SentenceAxiom
                    { sentenceAxiomParameters = []
                    , sentenceAxiomPattern =
                        embedParsedPattern $
                            StringLiteralF $ Const (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAxiom
                )
            )
        , success
            "axiom { sv1 , sv2 } \"a\" [ \"b\" ] "
            ( SentenceAxiomSentence
                ( SentenceAxiom
                    { sentenceAxiomParameters =
                        [ SortVariable (testId "sv1")
                        , SortVariable (testId "sv2")
                        ]
                    , sentenceAxiomPattern =
                        embedParsedPattern $
                            StringLiteralF $ Const (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAxiom
                )
            )
        , FailureWithoutMessage
            [ ""
            , "{sv1}\"a\"[\"b\"]"
            , "axiom\"a\"[\"b\"]"
            , -- , "axiom{}\"a\"[\"b\"]" See the TODO above.
              "axiom{sv1}[\"b\"]"
            , "axiom{sv1}\"a\""
            ]
        ]

sentenceClaimParserTests :: [TestTree]
sentenceClaimParserTests =
    parseTree
        parseSentence
        [ success
            "claim{sv1}\"a\"[\"b\"]"
            ( SentenceClaimSentence . SentenceClaim $
                ( SentenceAxiom
                    { sentenceAxiomParameters = [SortVariable (testId "sv1")]
                    , sentenceAxiomPattern =
                        embedParsedPattern $
                            StringLiteralF $ Const (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAxiom
                )
            )
        , {- TODO(virgil): The Scala parser allows empty sort variable lists
             while the semantics-of-k document does not. -}
          success
            "claim{}\"a\"[\"b\"]"
            ( SentenceClaimSentence . SentenceClaim $
                ( SentenceAxiom
                    { sentenceAxiomParameters = []
                    , sentenceAxiomPattern =
                        embedParsedPattern $
                            StringLiteralF $ Const (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAxiom
                )
            )
        , success
            "claim { sv1 , sv2 } \"a\" [ \"b\" ] "
            ( SentenceClaimSentence . SentenceClaim $
                ( SentenceAxiom
                    { sentenceAxiomParameters =
                        [ SortVariable (testId "sv1")
                        , SortVariable (testId "sv2")
                        ]
                    , sentenceAxiomPattern =
                        embedParsedPattern $
                            StringLiteralF $ Const (StringLiteral "a")
                    , sentenceAxiomAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceAxiom
                )
            )
        , FailureWithoutMessage
            [ ""
            , "{sv1}\"a\"[\"b\"]"
            , "claim\"a\"[\"b\"]"
            , -- , "claim{}\"a\"[\"b\"]" See the TODO above.
              "claim{sv1}[\"b\"]"
            , "claim{sv1}\"a\""
            ]
        ]

sentenceImportParserTests :: [TestTree]
sentenceImportParserTests =
    parseTree
        parseSentence
        [ success
            "import M[\"b\"]"
            ( SentenceImportSentence
                ( SentenceImport
                    { sentenceImportModuleName = ModuleName "M"
                    , sentenceImportAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "b")
                            ]
                    } ::
                    ParsedSentenceImport
                )
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
    parseTree
        parseSentence
        [ success
            "sort s1 { sv1 } [ \"a\" ]"
            ( SentenceSortSentence
                ( SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = [sortVariable "sv1"]
                    , sentenceSortAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "a")
                            ]
                    } ::
                    ParsedSentenceSort
                )
            )
        , {- TODO(virgil): The Scala parser allows empty sort variable lists
             while the semantics-of-k document does not. -}
          success
            "sort s1 {} [ \"a\" ]"
            ( SentenceSortSentence
                ( SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "a")
                            ]
                    } ::
                    ParsedSentenceSort
                )
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
    parseTree
        parseSentence
        [ success
            "symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( SentenceSymbolSentence
                ( SentenceSymbol
                    { sentenceSymbolSymbol =
                        Symbol
                            { symbolConstructor = testId "sy1"
                            , symbolParams = [sortVariable "s1"]
                            }
                    , sentenceSymbolSorts = [sortVariableSort "s1"]
                    , sentenceSymbolResultSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes =
                        Attributes
                            [ embedParsedPattern $
                                StringLiteralF $ Const (StringLiteral "a")
                            ]
                    } ::
                    ParsedSentenceSymbol
                )
            )
        , success
            "symbol sy1 {} () : s1 [] "
            ( SentenceSymbolSentence
                ( SentenceSymbol
                    { sentenceSymbolSymbol =
                        Symbol
                            { symbolConstructor = testId "sy1"
                            , symbolParams = []
                            }
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort = sortVariableSort "s1"
                    , sentenceSymbolAttributes = Attributes []
                    } ::
                    ParsedSentenceSymbol
                )
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
    parseTree
        parseSentence
        [ success
            "hooked-sort s1 { sv1 } [ \"a\" ]"
            ( SentenceHookSentence
                ( SentenceHookedSort
                    SentenceSort
                        { sentenceSortName = testId "s1"
                        , sentenceSortParameters = [sortVariable "sv1"]
                        , sentenceSortAttributes =
                            Attributes
                                [ embedParsedPattern $
                                    StringLiteralF $ Const (StringLiteral "a")
                                ]
                        } ::
                    ParsedSentenceHook
                )
            )
        , {- TODO(virgil): The Scala parser allows empty sort variable lists
             while the semantics-of-k document does not. -}
          success
            "hooked-sort s1 {} [ \"a\" ]"
            ( SentenceHookSentence
                ( SentenceHookedSort
                    SentenceSort
                        { sentenceSortName = testId "s1"
                        , sentenceSortParameters = []
                        , sentenceSortAttributes =
                            Attributes
                                [ embedParsedPattern $
                                    StringLiteralF $ Const (StringLiteral "a")
                                ]
                        } ::
                    ParsedSentenceHook
                )
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
    parseTree
        parseSentence
        [ success
            "hooked-symbol sy1 { s1 } ( s1 ) : s1 [\"a\"] "
            ( SentenceHookSentence
                ( SentenceHookedSymbol
                    SentenceSymbol
                        { sentenceSymbolSymbol =
                            Symbol
                                { symbolConstructor = testId "sy1"
                                , symbolParams = [sortVariable "s1"]
                                }
                        , sentenceSymbolSorts = [sortVariableSort "s1"]
                        , sentenceSymbolResultSort = sortVariableSort "s1"
                        , sentenceSymbolAttributes =
                            Attributes
                                [ embedParsedPattern $
                                    StringLiteralF $ Const (StringLiteral "a")
                                ]
                        } ::
                    ParsedSentenceHook
                )
            )
        , success
            "hooked-symbol sy1 {} () : s1 [] "
            ( SentenceHookSentence
                ( SentenceHookedSymbol
                    SentenceSymbol
                        { sentenceSymbolSymbol =
                            Symbol
                                { symbolConstructor = testId "sy1"
                                , symbolParams = []
                                }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort = sortVariableSort "s1"
                        , sentenceSymbolAttributes = Attributes []
                        } ::
                    ParsedSentenceHook
                )
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
    parseTree
        parseAttributes
        [ success
            "[\"a\"]"
            ( Attributes
                [embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")]
            )
        , success "[]" (Attributes [])
        , success
            "[\"a\", \"b\"]"
            ( Attributes
                [ embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")
                , embedParsedPattern $ StringLiteralF $ Const (StringLiteral "b")
                ]
            )
        , FailureWithoutMessage ["", "a", "\"a\"", "[\"a\" \"a\"]"]
        ]

moduleParserTests :: [TestTree]
moduleParserTests =
    parseTree
        parseModule
        [ success
            "module MN sort c{}[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ asSentence
                        ( SentenceSort
                            { sentenceSortName = testId "c"
                            , sentenceSortParameters = []
                            , sentenceSortAttributes = Attributes []
                            } ::
                            ParsedSentenceSort
                        )
                    ]
                , moduleAttributes =
                    Attributes
                        [embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")]
                }
        , success
            "module MN sort c{}[] sort c{}[] endmodule [\"a\"]"
            Module
                { moduleName = ModuleName "MN"
                , moduleSentences =
                    [ SentenceSortSentence
                        SentenceSort
                            { sentenceSortName = testId "c"
                            , sentenceSortParameters = []
                            , sentenceSortAttributes = Attributes []
                            }
                    , SentenceSortSentence
                        SentenceSort
                            { sentenceSortName = testId "c"
                            , sentenceSortParameters = []
                            , sentenceSortAttributes = Attributes []
                            }
                    ]
                , moduleAttributes =
                    Attributes
                        [embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")]
                }
        , success
            "module MN endmodule []"
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
    parseTree
        parseDefinition
        [ success
            "[\"a\"] module M sort c{}[] endmodule [\"b\"]"
            Definition
                { definitionAttributes =
                    Attributes
                        [embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")]
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ asSentence
                                ( SentenceSort
                                    { sentenceSortName = testId "c"
                                    , sentenceSortParameters = []
                                    , sentenceSortAttributes = Attributes []
                                    } ::
                                    ParsedSentenceSort
                                )
                            ]
                        , moduleAttributes =
                            Attributes
                                [ embedParsedPattern $
                                    StringLiteralF $ Const (StringLiteral "b")
                                ]
                        }
                    ]
                }
        , success
            ( pack $
                "[\"a\"] "
                    ++ "module M sort c{}[] endmodule [\"b\"] "
                    ++ "module N sort d{}[] endmodule [\"e\"]"
            )
            Definition
                { definitionAttributes =
                    Attributes
                        [embedParsedPattern $ StringLiteralF $ Const (StringLiteral "a")]
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M"
                        , moduleSentences =
                            [ asSentence
                                ( SentenceSort
                                    { sentenceSortName = testId "c"
                                    , sentenceSortParameters = []
                                    , sentenceSortAttributes = Attributes []
                                    } ::
                                    ParsedSentenceSort
                                )
                            ]
                        , moduleAttributes =
                            Attributes
                                [ embedParsedPattern $
                                    StringLiteralF $ Const (StringLiteral "b")
                                ]
                        }
                    , Module
                        { moduleName = ModuleName "N"
                        , moduleSentences =
                            [ asSentence
                                ( SentenceSort
                                    { sentenceSortName = testId "d"
                                    , sentenceSortParameters = []
                                    , sentenceSortAttributes = Attributes []
                                    } ::
                                    ParsedSentenceSort
                                )
                            ]
                        , moduleAttributes =
                            Attributes
                                [ embedParsedPattern $
                                    StringLiteralF $ Const (StringLiteral "e")
                                ]
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

sortVariableSort :: Text -> Sort
sortVariableSort name = SortVariableSort (sortVariable name)

sortVariable :: Text -> SortVariable
sortVariable name = SortVariable (testId name)
