module Data.Kore.MetaML.LiftTest where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertEqual, testCase)

import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.Builders
import           Data.Kore.MetaML.BuildersImpl
import           Data.Kore.MetaML.Lift
import           Data.Kore.MetaML.Unlift

variablePattern :: String -> Sort Meta -> CommonMetaPattern
variablePattern name sort = fillCheckSort sort (unparameterizedVariable_ name)

liftTests :: TestTree
liftTests =
    testGroup
        "Lifting Tests"
        [ testCase "Lifting an Id"
            (prettyAssertEqual
                (Fix (StringLiteralPattern (StringLiteral "object")))
                (liftToMeta (Id "object" :: Id Object))
            )
        , testCase "Lifting a Meta Pattern"
            (prettyAssertEqual
                metaStringPattern
                (liftToMeta unifiedStringPattern)
            )
        , testCase "Lifting Bottom"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead BottomPatternType)
                        [ variablePattern "#a" sortMetaSort ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        ( BottomPattern Bottom
                            { bottomSort = SortVariableSort
                                (SortVariable (Id "a"))
                            }
                        )
                    ::UnifiedPattern)
                )
            )
        , testCase "Lifting Top"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead TopPatternType)
                        [ variablePattern "#a" sortMetaSort ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        ( TopPattern Top
                            { topSort =
                                SortVariableSort (SortVariable (Id "a"))
                            }
                        )
                    ::UnifiedPattern)
                )
            )
        , testCase "Lifting Ceil"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead CeilPatternType)
                        [ variablePattern "#b" sortMetaSort
                        , variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (CeilPattern Ceil
                            { ceilResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , ceilOperandSort =
                                SortVariableSort (SortVariable (Id "b"))
                            , ceilChild = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Floor"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead FloorPatternType)
                        [ variablePattern "#b" sortMetaSort
                        , variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (FloorPattern Floor
                            { floorResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , floorOperandSort =
                                SortVariableSort (SortVariable (Id "b"))
                            , floorChild = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Equals"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead EqualsPatternType)
                        [ variablePattern "#b" sortMetaSort
                        , variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (EqualsPattern Equals
                            { equalsResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , equalsOperandSort =
                                SortVariableSort (SortVariable (Id "b"))
                            , equalsFirst = unifiedStringPattern
                            , equalsSecond = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting In"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead InPatternType)
                        [ variablePattern "#b" sortMetaSort
                        , variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (InPattern In
                            { inResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , inOperandSort =
                                SortVariableSort (SortVariable (Id "b"))
                            , inContainedChild = unifiedStringPattern
                            , inContainingChild = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Forall"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead ForallPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , Fix
                            (apply variableHead
                                [ Fix (StringLiteralPattern (StringLiteral "x"))
                                , variablePattern "#a" sortMetaSort
                                ]
                            )
                        , Fix
                            (apply variableAsPatternHead
                                [ Fix
                                    (apply variableHead
                                        [ Fix
                                            (StringLiteralPattern
                                                (StringLiteral "x")
                                            )
                                        , variablePattern "#a" sortMetaSort
                                        ]
                                    )
                                ]
                            )
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (ForallPattern Forall
                            { forallSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , forallVariable = Variable
                                { variableName = Id "x"
                                , variableSort =
                                    SortVariableSort (SortVariable (Id "a"))
                                }
                            , forallChild =
                                ObjectPattern
                                    (VariablePattern Variable
                                        { variableName = Id "x"
                                        , variableSort = SortVariableSort
                                            (SortVariable (Id "a"))
                                        }
                                    )
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Exists"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead ExistsPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , Fix
                            (apply variableHead
                                [ Fix (StringLiteralPattern (StringLiteral "x"))
                                , variablePattern "#a" sortMetaSort
                                ]
                            )
                        , Fix
                            (apply variableAsPatternHead
                                [ Fix
                                    (apply variableHead
                                        [ Fix
                                            (StringLiteralPattern
                                                (StringLiteral "x")
                                            )
                                        , variablePattern "#a" sortMetaSort
                                        ]
                                    )
                                ]
                            )
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (ExistsPattern Exists
                            { existsSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , existsVariable = Variable
                                { variableName = Id "x"
                                , variableSort =
                                    SortVariableSort (SortVariable (Id "a"))
                                }
                            , existsChild =
                                ObjectPattern
                                    (VariablePattern Variable
                                        { variableName = Id "x"
                                        , variableSort = SortVariableSort
                                            (SortVariable (Id "a"))
                                        }
                                    )
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Variable Pattern"
            (prettyAssertEqual
                (Fix
                    (apply variableAsPatternHead
                        [ Fix
                            (apply variableHead
                                [ Fix (StringLiteralPattern (StringLiteral "x"))
                                , variablePattern "#a" sortMetaSort
                                ]
                            )
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (VariablePattern Variable
                            { variableName = Id "x"
                            , variableSort = SortVariableSort
                                (SortVariable (Id "a"))
                            }
                        )
                    )
                )
            )
        , testCase "Lifting an actual sort"
            (prettyAssertEqual
                (Fix
                    (apply consSortListHead
                        [ Fix
                            (apply (groundHead "#`Exp")
                                [ variablePattern "#v" sortMetaSort ]
                            )
                        , Fix (apply nilSortListHead [])
                        ]
                    )
                )
                (liftToMeta
                    [SortActualSort SortActual
                        { sortActualName = Id "Exp" :: Id Object
                        , sortActualSorts =
                            [ SortVariableSort (SortVariable (Id "v")) ]
                        }
                    ]
                )
            )
        , testCase "Lifting a Variable"
            (prettyAssertEqual
                (Fix
                    (apply consPatternListHead
                        [ Fix
                            (apply variableHead
                                [ Fix
                                    (StringLiteralPattern
                                        (StringLiteral "object")
                                    )
                                , variablePattern "#v" sortMetaSort
                                ]
                            )
                        , Fix (apply nilPatternListHead [])
                        ]
                    )
                )
                (liftToMeta
                    [ liftToMeta
                        Variable
                            { variableName = Id "object" :: Id Object
                            , variableSort =
                                SortVariableSort (SortVariable (Id "v"))
                            }
                    ]
                )
            )
        , testCase "Testing lifting a pure object pattern."
            (prettyAssertEqual
                ( Fix
                    ( apply (metaMLPatternHead NotPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , Fix
                            ( apply (metaMLPatternHead TopPatternType)
                                [ variablePattern "#a" sortMetaSort ]
                            )
                        ]
                    )
                )
                ( liftToMeta
                    ( ObjectPattern
                        ( NotPattern Not
                            { notSort = SortVariableSort (SortVariable (Id "a"))
                            , notChild = ObjectPattern
                                ( TopPattern Top
                                    { topSort = SortVariableSort
                                        (SortVariable (Id "a"))
                                    }
                                )
                            }
                        )
                    ::UnifiedPattern)
                )
            )
        , testCase "Lifting And pattern"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead AndPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (AndPattern And
                            { andSort = SortVariableSort (SortVariable (Id "a"))
                            , andFirst = unifiedStringPattern
                            , andSecond = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Or pattern"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead OrPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (OrPattern Or
                            { orSort = SortVariableSort (SortVariable (Id "a"))
                            , orFirst = unifiedStringPattern
                            , orSecond = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Iff pattern"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead IffPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (IffPattern Iff
                            { iffSort = SortVariableSort (SortVariable (Id "a"))
                            , iffFirst = unifiedStringPattern
                            , iffSecond = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Implies pattern"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead ImpliesPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (ImpliesPattern Implies
                            { impliesSort = SortVariableSort (SortVariable (Id "a"))
                            , impliesFirst = unifiedStringPattern
                            , impliesSecond = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Not"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead NotPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (NotPattern Not
                            { notSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , notChild = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Rewrites pattern"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead RewritesPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (RewritesPattern Rewrites
                            { rewritesSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , rewritesFirst = unifiedStringPattern
                            , rewritesSecond = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Domain Value"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead DomainValuePatternType)
                        [ variablePattern "#Int" sortMetaSort
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (DomainValuePattern DomainValue
                            { domainValueSort =
                                SortVariableSort (SortVariable (Id "Int"))
                            , domainValueChild =
                                unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Application"
            (prettyAssertEqual
                (Fix
                    (apply (groundHead "#`test")
                        [ variablePattern "#Int" sortMetaSort
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (apply
                            SymbolOrAlias
                                { symbolOrAliasConstructor = Id "test"
                                , symbolOrAliasParams =
                                    [ SortVariableSort (SortVariable (Id "Int"))
                                    ]
                                }
                            [unifiedStringPattern]
                        )
                    )
                )
            )
        , testCase "Lifting Next"
            (prettyAssertEqual
                (Fix
                    (apply (metaMLPatternHead NextPatternType)
                        [ variablePattern "#a" sortMetaSort
                        , metaStringPattern
                        ]
                    )
                )
                (liftToMeta
                    (ObjectPattern
                        (NextPattern Next
                            { nextSort =
                                SortVariableSort (SortVariable (Id "a"))
                            , nextChild = unifiedStringPattern
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Attributes"
            (prettyAssertEqual
                (Attributes [SentenceMetaPattern metaStringPattern])
                (liftAttributes (Attributes [unifiedStringPattern]))
            )
        , testCase "Lifting Meta Alias Declaration"
            (prettyAssertEqual
                [ SentenceAliasSentence SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id "#alias"
                        , aliasParams = []
                        }
                    , sentenceAliasSorts = []
                    , sentenceAliasResultSort =
                        SortVariableSort (SortVariable (Id "#a"))
                    , sentenceAliasAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (MetaSentence $ SentenceAliasSentence SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = Id "#alias"
                            , aliasParams = []
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                                SortVariableSort (SortVariable (Id "#a"))
                        , sentenceAliasAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Object Alias Declaration"
            (prettyAssertEqual
                [ SentenceSymbolSentence (symbol_ "#`alias" [] patternMetaSort)
                ]
                (liftSentence
                    (ObjectSentence $ SentenceAliasSentence SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = Id "alias"
                            , aliasParams = []
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                        , sentenceAliasAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Object Symbol Declaration"
            (prettyAssertEqual
                [ SentenceSymbolSentence
                    (symbol_ "#`alias"
                        [sortMetaSort, patternMetaSort]
                        patternMetaSort
                    )
                , SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#s"]
                    , sentenceAxiomPattern =
                        SentenceMetaPattern $ Fix
                            (EqualsPattern Equals
                                { equalsOperandSort = patternMetaSort
                                , equalsResultSort =
                                    SortVariableSort (sortParameter "#s")
                                , equalsFirst =
                                    Fix
                                        (apply (groundHead "#`alias")
                                            [ variablePattern
                                                "#a"
                                                sortMetaSort
                                            , variablePattern
                                                "#P1"
                                                patternMetaSort
                                            ]
                                        )
                                , equalsSecond = Fix
                                    (apply applicationHead
                                        [ Fix
                                            (apply symbolHead
                                                [ Fix
                                                    (StringLiteralPattern
                                                        (StringLiteral "alias")
                                                    )
                                                , Fix
                                                    (apply consSortListHead
                                                        [ variablePattern
                                                            "#a"
                                                            sortMetaSort
                                                        , Fix
                                                            (apply
                                                                nilSortListHead
                                                                []
                                                            )
                                                        ]
                                                    )
                                                , Fix
                                                    (apply consSortListHead
                                                        [ variablePattern
                                                            "#a"
                                                            sortMetaSort
                                                        , Fix
                                                            (apply
                                                                nilSortListHead
                                                                []
                                                            )
                                                        ]
                                                    )
                                                , variablePattern
                                                    "#a"
                                                    sortMetaSort
                                                ]
                                            )
                                        , Fix
                                            (apply consPatternListHead
                                                [ variablePattern
                                                    "#P1"
                                                    patternMetaSort
                                                , Fix
                                                    (apply nilPatternListHead
                                                        []
                                                    )
                                                ]
                                            )
                                        ]
                                    )
                                }
                            )
                    , sentenceAxiomAttributes = Attributes []
                    }
                , SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [ sortParameter "#s" ]
                    , sentenceAxiomPattern = SentenceMetaPattern $ Fix
                        (ImpliesPattern Implies
                            { impliesSort =
                                SortVariableSort (sortParameter "#s")
                            , impliesFirst =
                                Fix
                                    (apply
                                        (sortsDeclaredHead
                                            (SortVariableSort
                                                (sortParameter "#s")
                                            )
                                        )
                                        [ Fix
                                            (apply consSortListHead
                                                [ variablePattern
                                                    "#a"
                                                    sortMetaSort
                                                , Fix
                                                    (apply
                                                        nilSortListHead
                                                        []
                                                    )
                                                ]
                                            )

                                        ]
                                    )
                            , impliesSecond =
                                Fix
                                    (apply
                                        (symbolDeclaredHead
                                            (SortVariableSort
                                                (sortParameter "#s")
                                            )
                                        )
                                        [ Fix
                                            (apply symbolHead
                                                [ Fix
                                                    (StringLiteralPattern
                                                        (StringLiteral "alias")
                                                    )
                                                , Fix
                                                    (apply consSortListHead
                                                        [ variablePattern
                                                            "#a"
                                                            sortMetaSort
                                                        , Fix
                                                            (apply
                                                                nilSortListHead
                                                                []
                                                            )
                                                        ]
                                                    )
                                                , Fix
                                                    (apply consSortListHead
                                                        [ variablePattern
                                                            "#a"
                                                            sortMetaSort
                                                        , Fix
                                                            (apply
                                                                nilSortListHead
                                                                []
                                                            )
                                                        ]
                                                    )
                                                , variablePattern
                                                    "#a"
                                                    sortMetaSort
                                                ]
                                            )
                                        ]
                                    )
                            }
                        )
                    , sentenceAxiomAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (ObjectSentence $ SentenceSymbolSentence SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = Id "alias"
                            , symbolParams = [SortVariable (Id "a")]
                            }
                        , sentenceSymbolSorts =
                            [ SortVariableSort (SortVariable (Id "a")) ]
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                        , sentenceSymbolAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Meta Symbol Declaration"
            (prettyAssertEqual
                [ SentenceSymbolSentence SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id "#symbol"
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort =
                        SortVariableSort (SortVariable (Id "#a"))
                    , sentenceSymbolAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (MetaSentence $ SentenceSymbolSentence SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = Id "#symbol"
                            , symbolParams = []
                            }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (Id "#a"))
                        , sentenceSymbolAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Sort Declaration"
            (prettyAssertEqual
                [ SentenceSymbolSentence SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id "#`List"
                        , symbolParams = []
                        }
                    , sentenceSymbolSorts = [sortMetaSort]
                    , sentenceSymbolResultSort = sortMetaSort
                    , sentenceSymbolAttributes = Attributes []
                    }
                , SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [ sortParameter "#s" ]
                    , sentenceAxiomPattern = SentenceMetaPattern
                        (Fix
                            (EqualsPattern Equals
                                { equalsOperandSort = sortMetaSort
                                , equalsResultSort =
                                    SortVariableSort (sortParameter "#s")
                                , equalsFirst = Fix
                                    (apply (groundHead "#`List")
                                        [ variablePattern "#a" sortMetaSort ]
                                    )
                                , equalsSecond = Fix
                                    (apply sortHead
                                        [ Fix
                                            (StringLiteralPattern
                                                (StringLiteral "List")
                                            )
                                        , Fix
                                            (apply consSortListHead
                                                [ variablePattern "#a"
                                                    sortMetaSort
                                                , Fix (apply nilSortListHead [])
                                                ]
                                            )
                                        ]
                                    )
                                }
                            )
                        )
                    , sentenceAxiomAttributes = Attributes []
                    }
                , SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#s"]
                    , sentenceAxiomPattern = SentenceMetaPattern
                        (Fix
                            (ImpliesPattern Implies
                                { impliesSort =
                                    SortVariableSort (sortParameter "#s")
                                , impliesFirst = Fix
                                    (apply
                                        (sortsDeclaredHead
                                            (SortVariableSort
                                                (sortParameter "#s")
                                            )
                                        )
                                        [ Fix
                                            (apply consSortListHead
                                                [ variablePattern "#a"
                                                    sortMetaSort
                                                , Fix (apply nilSortListHead [])
                                                ]
                                            )
                                        ]
                                    )
                                , impliesSecond = Fix
                                    (apply
                                        (sortDeclaredHead
                                            (SortVariableSort
                                                (sortParameter "#s")
                                            )
                                        )
                                        [ Fix
                                            (apply (groundHead "#`List")
                                                [ variablePattern "#a"
                                                    sortMetaSort
                                                ]
                                            )
                                        ]
                                    )
                                }
                            )
                        )
                    , sentenceAxiomAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (ObjectSentence $ SentenceSortSentence SentenceSort
                        { sentenceSortName = Id "List"
                        , sentenceSortParameters = [SortVariable (Id "a")]
                        , sentenceSortAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Axiom topped in Object Pattern"
            (prettyAssertEqual
                [ SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#a"]
                    , sentenceAxiomPattern = SentenceMetaPattern $ Fix
                        (ImpliesPattern Implies
                            { impliesSort = patternMetaSort
                            , impliesFirst = Fix
                                (apply (sortsDeclaredHead patternMetaSort)
                                    [ Fix
                                        (apply consSortListHead
                                            [ variablePattern "#a" sortMetaSort
                                            , Fix (apply nilSortListHead [])
                                            ]
                                        )
                                    ]
                                )
                            , impliesSecond = Fix
                                (apply (provableHead patternMetaSort)
                                    [ Fix
                                        (apply (metaMLPatternHead TopPatternType)
                                            [variablePattern "#a" sortMetaSort]
                                        )
                                    ]
                                )
                            }
                        )
                    , sentenceAxiomAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (MetaSentence $ SentenceAxiomSentence SentenceAxiom
                        { sentenceAxiomParameters =
                            [ ObjectSortVariable (SortVariable (Id "a"))
                            , MetaSortVariable (SortVariable (Id "#a"))
                            ]
                        , sentenceAxiomPattern = ObjectPattern
                            (TopPattern
                                (Top
                                    (SortVariableSort (SortVariable (Id "a")))
                                )
                            )
                        , sentenceAxiomAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Axiom topped in Meta Pattern"
            (prettyAssertEqual
                [ SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = []
                    , sentenceAxiomPattern = SentenceMetaPattern $ Fix
                        (ImpliesPattern Implies
                            { impliesSort = charListMetaSort
                            , impliesFirst = Fix
                                (apply (sortsDeclaredHead charListMetaSort)
                                    [ Fix (apply nilSortListHead []) ]
                                )
                            , impliesSecond = metaStringPattern
                            }
                        )
                    , sentenceAxiomAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (MetaSentence $ SentenceAxiomSentence SentenceAxiom
                        { sentenceAxiomParameters = []
                        , sentenceAxiomPattern = unifiedStringPattern
                        , sentenceAxiomAttributes = Attributes []
                        }
                    )
                )
            )
        , testCase "Lifting Import Sentence"
            (prettyAssertEqual
                [ metaSentenceImport ]
                (liftSentence koreSentenceImport)
            )
        , testCase "Lifting Module"
            (prettyAssertEqual
                simpleMetaModule
                (liftModule simpleKoreModule)
            )
        , testCase "Lifting Definition"
            (prettyAssertEqual
                simpleMetaDefinition
                (liftDefinition simpleKoreDefinition)
            )
        ]
--TODO(traiansf): add more tests covering all sentences (esp. axiom),
-- modules and definitions

prettyAssertEqual :: (Eq a, Show a, PrettyPrint a) => a -> a -> IO ()
prettyAssertEqual x y =
    assertEqual
        ( "Expected:\n"
          ++ prettyPrintToString x
          ++ "\nActual\n"
          ++ prettyPrintToString y
        )
        x
        y

testLiftUnlift
    :: (LiftableToMetaML a, UnliftableFromMetaML a)
    => String
    -> a
    -> CommonMetaPattern
    -> IO ()
testLiftUnlift message mixed metaPattern =
    testGroup message
        [
            testCase "Lifting"
        ]


natSort :: Sort Object
natSort = SortActualSort SortActual
    { sortActualName = Id "Nat"
    , sortActualSorts = []
    }

stringPattern :: Pattern Meta Variable child
stringPattern = StringLiteralPattern (StringLiteral "a")

unifiedStringPattern :: UnifiedPattern
unifiedStringPattern = MetaPattern stringPattern

metaStringPattern :: CommonMetaPattern
metaStringPattern = Fix stringPattern

sentenceImport :: Sentence Meta sortParam pat variable
sentenceImport =
    SentenceImportSentence SentenceImport
        { sentenceImportModuleName = ModuleName "MODULE"
        , sentenceImportAttributes = Attributes []
        }

koreSentenceImport :: KoreSentence
koreSentenceImport = MetaSentence sentenceImport

metaSentenceImport :: MetaSentence
metaSentenceImport = sentenceImport

simpleKoreModule :: KoreModule
simpleKoreModule =
    Module
        { moduleName = ModuleName "MODULE"
        , moduleSentences = [koreSentenceImport]
        , moduleAttributes = Attributes []
        }

simpleMetaModule :: MetaModule
simpleMetaModule =
    Module
        { moduleName = ModuleName "MODULE"
        , moduleSentences = [metaSentenceImport]
        , moduleAttributes = Attributes []
        }

simpleKoreDefinition :: KoreDefinition
simpleKoreDefinition =
    Definition
        { definitionModules = [simpleKoreModule]
        , definitionAttributes = Attributes []
        }

simpleMetaDefinition :: MetaDefinition
simpleMetaDefinition =
    Definition
        { definitionModules = [simpleMetaModule]
        , definitionAttributes = Attributes []
        }
