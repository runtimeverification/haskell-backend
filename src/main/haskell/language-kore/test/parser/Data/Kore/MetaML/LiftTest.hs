module Data.Kore.MetaML.LiftTest where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertEqual, testCase)

import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.Builders
import           Data.Kore.MetaML.BuildersImpl
import           Data.Kore.MetaML.Lift

variablePattern :: String -> Sort Meta -> CommonMetaPattern
variablePattern name sort = fillCheckSort sort (unparameterizedVariable_ name)

liftTests :: TestTree
liftTests =
    testGroup
        "Lifting Tests"
        [ testCase "Lifting an Id"
            (assertEqual ""
                (Fix (StringLiteralPattern (StringLiteral "object")))
                (liftToMeta (Id "object" :: Id Object))
            )
        , testCase "Lifting a Meta Pattern"
            (assertEqual ""
                metaStringPattern
                (liftToMeta unifiedStringPattern)
            )
        , testCase "Lifting Bottom"
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
                                (ObjectPattern
                                    (VariablePattern Variable
                                        { variableName = Id "x"
                                        , variableSort = SortVariableSort
                                            (SortVariable (Id "a"))
                                        }
                                    )
                                )
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Exists"
            (assertEqual ""
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
                                (ObjectPattern
                                    (VariablePattern Variable
                                        { variableName = Id "x"
                                        , variableSort = SortVariableSort
                                            (SortVariable (Id "a"))
                                        }
                                    )
                                )
                            }
                        )
                    )
                )
            )
        , testCase "Lifting Variable Pattern"
            (assertEqual ""
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
            (assertEqual ""
                (Fix
                    (apply consSortListHead
                        [ Fix
                            (apply (groundHead "#`Exp")
                                [ (variablePattern "#v" sortMetaSort) ]
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
            (assertEqual ""
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
                        (Variable
                            { variableName = Id "object" :: Id Object
                            , variableSort =
                                SortVariableSort (SortVariable (Id "v"))
                            }
                        )
                    ]
                )
            )
        , testCase "Testing lifting a pure object pattern."
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
            (assertEqual ""
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
                            (SymbolOrAlias
                                { symbolOrAliasConstructor = Id "test"
                                , symbolOrAliasParams =
                                    [ SortVariableSort (SortVariable (Id "Int"))
                                    ]
                                }
                            )
                            [unifiedStringPattern]
                        )
                    )
                )
            )
        , testCase "Lifting Next"
            (assertEqual ""
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
            (assertEqual ""
                (Attributes [metaStringPattern])
                (liftAttributes (Attributes [unifiedStringPattern]))
            )
        , testCase "Lifting Meta Alias Declaration"
            (assertEqual ""
                [ AliasMetaSentence SentenceAlias
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
                    (MetaSentenceAliasSentence SentenceAlias
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
            (assertEqual ""
                [ SymbolMetaSentence (symbol_ "#`alias" [] patternMetaSort) ]
                (liftSentence
                    (ObjectSentenceAliasSentence SentenceAlias
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
            (assertEqual ""
                [ SymbolMetaSentence (symbol_ "#`alias" [] patternMetaSort)
                , AxiomMetaSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#s"]
                    , sentenceAxiomPattern =
                        Fix
                            (EqualsPattern Equals
                                { equalsOperandSort = patternMetaSort
                                , equalsResultSort =
                                    SortVariableSort (sortParameter "#s")
                                , equalsFirst =
                                    Fix (apply (groundHead "#`alias") [])
                                , equalsSecond = Fix
                                    (apply applicationHead
                                        [ Fix
                                            (apply symbolHead
                                                [ Fix
                                                    (StringLiteralPattern
                                                        (StringLiteral "alias")
                                                    )
                                                , Fix (apply nilSortListHead [])
                                                , Fix (apply nilSortListHead [])
                                                , variablePattern
                                                    "#a"
                                                    sortMetaSort
                                                ]
                                            )
                                        , Fix (apply nilPatternListHead [])
                                        ]
                                    )
                                }
                            )
                    , sentenceAxiomAttributes = Attributes []
                    }
                , AxiomMetaSentence SentenceAxiom
                    { sentenceAxiomParameters = [ sortParameter "#s" ]
                    , sentenceAxiomPattern = Fix
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
                                        [Fix (apply nilSortListHead [])]
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
                                                , Fix (apply nilSortListHead [])
                                                , Fix (apply nilSortListHead [])
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
                    (ObjectSentenceSymbolSentence SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = Id "alias"
                            , symbolParams = []
                            }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                        , sentenceSymbolAttributes = Attributes []
                        }
                    )
                )
            )
        ]

stringPattern :: Pattern Meta Variable child
stringPattern = StringLiteralPattern (StringLiteral "a")

unifiedStringPattern :: UnifiedPattern
unifiedStringPattern = MetaPattern stringPattern

metaStringPattern :: CommonMetaPattern
metaStringPattern = Fix stringPattern
