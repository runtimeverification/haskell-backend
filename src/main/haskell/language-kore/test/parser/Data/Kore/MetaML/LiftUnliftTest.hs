{-# LANGUAGE FlexibleContexts #-}
module Data.Kore.MetaML.LiftUnliftTest where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (testCase)

import           Test.Tasty.HUnit.Extensions

import           Data.CallStack
import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
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
        [ testLiftUnlift "Id"
            (Fix (StringLiteralPattern (StringLiteral "object")))
            (Id "object" :: Id Object)
        , testLiftUnlift "Meta Pattern"
            metaStringPattern
            unifiedStringPattern
        , testLiftUnlift "Bottom"
            (Fix
                (apply (metaMLPatternHead BottomPatternType)
                    [ variablePattern "#a" sortMetaSort ]
                )
            )
            (asKorePattern
                ( BottomPattern Bottom
                    { bottomSort = SortVariableSort
                        (SortVariable (Id "a" :: Id Object))
                    }
                )
            ::CommonKorePattern)
        , testLiftUnlift "Top"
            (Fix
                (apply (metaMLPatternHead TopPatternType)
                    [ variablePattern "#a" sortMetaSort ]
                )
            )
            (asKorePattern
                ( TopPattern Top
                    { topSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    }
                )
            ::CommonKorePattern)
        , testLiftUnlift "Ceil"
            (Fix
                (apply (metaMLPatternHead CeilPatternType)
                    [ variablePattern "#b" sortMetaSort
                    , variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (CeilPattern Ceil
                    { ceilResultSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , ceilOperandSort =
                        SortVariableSort (SortVariable (Id "b"))
                    , ceilChild = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Floor"
            (Fix
                (apply (metaMLPatternHead FloorPatternType)
                    [ variablePattern "#b" sortMetaSort
                    , variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (FloorPattern Floor
                    { floorResultSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , floorOperandSort =
                        SortVariableSort (SortVariable (Id "b"))
                    , floorChild = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Equals"
            (Fix
                (apply (metaMLPatternHead EqualsPatternType)
                    [ variablePattern "#b" sortMetaSort
                    , variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (EqualsPattern Equals
                    { equalsResultSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , equalsOperandSort =
                        SortVariableSort (SortVariable (Id "b"))
                    , equalsFirst = unifiedStringPattern
                    , equalsSecond = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "In"
            (Fix
                (apply (metaMLPatternHead InPatternType)
                    [ variablePattern "#b" sortMetaSort
                    , variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (InPattern In
                    { inResultSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , inOperandSort =
                        SortVariableSort (SortVariable (Id "b"))
                    , inContainedChild = unifiedStringPattern
                    , inContainingChild = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Forall"
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
            (asKorePattern
                (ForallPattern Forall
                    { forallSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , forallVariable = Variable
                        { variableName = Id "x"
                        , variableSort =
                            SortVariableSort (SortVariable (Id "a"))
                        }
                    , forallChild =
                        asKorePattern
                            (VariablePattern Variable
                                { variableName = Id "x" :: Id Object
                                , variableSort = SortVariableSort
                                    (SortVariable (Id "a"))
                                }
                            )
                    }
                )
            )
        , testLiftUnlift "Exists"
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
            (asKorePattern
                (ExistsPattern Exists
                    { existsSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , existsVariable = Variable
                        { variableName = Id "x"
                        , variableSort =
                            SortVariableSort (SortVariable (Id "a"))
                        }
                    , existsChild =
                        asKorePattern
                            (VariablePattern Variable
                                { variableName = Id "x" :: Id Object
                                , variableSort = SortVariableSort
                                    (SortVariable (Id "a"))
                                }
                            )
                    }
                )
            )
        , testLiftUnlift "Variable Pattern"
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
            (asKorePattern
                (VariablePattern Variable
                    { variableName = Id "x" :: Id Object
                    , variableSort = SortVariableSort
                        (SortVariable (Id "a"))
                    }
                )
            )
        , testLiftUnlift "An actual sort"
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
            [SortActualSort SortActual
                { sortActualName = Id "Exp" :: Id Object
                , sortActualSorts =
                    [ SortVariableSort (SortVariable (Id "v")) ]
                }
            ]
        , testLiftUnlift "Meta Pattern List"
            (Fix
                (apply consPatternListHead
                    [ metaStringPattern
                    , Fix (apply nilPatternListHead [])
                    ]
                )
            )
            [metaStringPattern]
        , testLiftUnlift "A Variable"
            (Fix
                (apply variableHead
                    [ Fix (StringLiteralPattern (StringLiteral "object"))
                    , variablePattern "#v" sortMetaSort
                    ]
                )
            )
            Variable
                { variableName = Id "object" :: Id Object
                , variableSort =
                    SortVariableSort (SortVariable (Id "v"))
                }
        , testLiftUnlift "A pure object pattern."
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
            ( asKorePattern
                ( NotPattern Not
                    { notSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , notChild = asKorePattern
                        ( TopPattern Top
                            { topSort = SortVariableSort
                                (SortVariable (Id "a" :: Id Object))
                            }
                        )
                    }
                )
            ::CommonKorePattern)
        , testLiftUnlift "And pattern"
            (Fix
                (apply (metaMLPatternHead AndPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (AndPattern And
                    { andSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , andFirst = unifiedStringPattern
                    , andSecond = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Or pattern"
            (Fix
                (apply (metaMLPatternHead OrPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (OrPattern Or
                    { orSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , orFirst = unifiedStringPattern
                    , orSecond = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Iff pattern"
            (Fix
                (apply (metaMLPatternHead IffPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (IffPattern Iff
                    { iffSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , iffFirst = unifiedStringPattern
                    , iffSecond = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Implies pattern"
            (Fix
                (apply (metaMLPatternHead ImpliesPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (ImpliesPattern Implies
                    { impliesSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , impliesFirst = unifiedStringPattern
                    , impliesSecond = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Not"
            (Fix
                (apply (metaMLPatternHead NotPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (NotPattern Not
                    { notSort =
                        SortVariableSort (SortVariable (Id "a" :: Id Object))
                    , notChild = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Rewrites pattern"
            (Fix
                (apply (metaMLPatternHead RewritesPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (RewritesPattern Rewrites
                    { rewritesSort =
                        SortVariableSort (SortVariable (Id "a"))
                    , rewritesFirst = unifiedStringPattern
                    , rewritesSecond = unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Domain Value"
            (Fix
                (apply (metaMLPatternHead DomainValuePatternType)
                    [ variablePattern "#Int" sortMetaSort
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (DomainValuePattern DomainValue
                    { domainValueSort =
                        SortVariableSort (SortVariable (Id "Int"))
                    , domainValueChild =
                        unifiedStringPattern
                    }
                )
            )
        , testLiftUnlift "Application"
            (Fix
                (apply (groundHead "#`test")
                    [ variablePattern "#Int" sortMetaSort
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (apply
                    SymbolOrAlias
                        { symbolOrAliasConstructor = Id "test" :: Id Object
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable (Id "Int"))
                            ]
                        }
                    [unifiedStringPattern]
                )
            )
        , testLiftUnlift "Next"
            (Fix
                (apply (metaMLPatternHead NextPatternType)
                    [ variablePattern "#a" sortMetaSort
                    , metaStringPattern
                    ]
                )
            )
            (asKorePattern
                (NextPattern Next
                    { nextSort =
                        SortVariableSort (SortVariable (Id "a"))
                    , nextChild = unifiedStringPattern
                    }
                )
            )
        , testCase "Lift Attributes"
            (prettyAssertEqual ""
                (Attributes [metaStringPattern])
                (liftAttributes (Attributes [unifiedStringPattern]))
            )
        , testCase "Lift Meta Alias Declaration"
            (prettyAssertEqual ""
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
                    (asSentence SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = Id "#alias" :: Id Meta
                            , aliasParams = []
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                                SortVariableSort (SortVariable (Id "#a"))
                        , sentenceAliasAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Object Alias Declaration"
            (prettyAssertEqual ""
                [ SentenceSymbolSentence (symbol_ "#`alias" [] patternMetaSort)
                ]
                (liftSentence
                    (asSentence SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = Id "alias" :: Id Object
                            , aliasParams = []
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                        , sentenceAliasAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Object Symbol Declaration"
            (prettyAssertEqual ""
                [ SentenceSymbolSentence
                    (symbol_ "#`alias"
                        [sortMetaSort, patternMetaSort]
                        patternMetaSort
                    )
                , SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#s"]
                    , sentenceAxiomPattern =
                        Fix
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
                    (asSentence SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = Id "alias" :: Id Object
                            , symbolParams = [SortVariable (Id "a")]
                            }
                        , sentenceSymbolSorts =
                            [ SortVariableSort (SortVariable (Id "a")) ]
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (Id "a"))
                        , sentenceSymbolAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Meta Symbol Declaration"
            (prettyAssertEqual ""
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
                    (asSentence SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = Id "#symbol" :: Id Meta
                            , symbolParams = []
                            }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (Id "#a"))
                        , sentenceSymbolAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Sort Declaration"
            (prettyAssertEqual ""
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
                    , sentenceAxiomPattern = Fix
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
                    , sentenceAxiomAttributes = Attributes []
                    }
                , SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#s"]
                    , sentenceAxiomPattern = Fix
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
                    , sentenceAxiomAttributes = Attributes []
                    }
                ]
                (liftSentence
                    (asSentence SentenceSort
                        { sentenceSortName = Id "List" :: Id Object
                        , sentenceSortParameters = [SortVariable (Id "a")]
                        , sentenceSortAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Axiom topped in Object Pattern"
            (prettyAssertEqual ""
                [ SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = [sortParameter "#a"]
                    , sentenceAxiomPattern = Fix
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
                    (asSentence SentenceAxiom
                        { sentenceAxiomParameters =
                            [ UnifiedObject (SortVariable (Id "a"))
                            , UnifiedMeta (SortVariable (Id "#a"))
                            ]
                        , sentenceAxiomPattern = asKorePattern
                            (TopPattern
                                (Top
                                    (SortVariableSort
                                        (SortVariable (Id "a" :: Id Object))
                                    )
                                )
                            )
                        , sentenceAxiomAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Axiom topped in Meta Pattern"
            (prettyAssertEqual ""
                [ SentenceAxiomSentence SentenceAxiom
                    { sentenceAxiomParameters = []
                    , sentenceAxiomPattern = Fix
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
                    (asSentence SentenceAxiom
                        { sentenceAxiomParameters = [] :: [UnifiedSortVariable]
                        , sentenceAxiomPattern = unifiedStringPattern
                        , sentenceAxiomAttributes =
                            Attributes [] :: KoreAttributes
                        }
                    )
                )
            )
        , testCase "Lift Import Sentence"
            (prettyAssertEqual ""
                [ metaSentenceImport ]
                (liftSentence koreSentenceImport)
            )
        , testCase "Lift Module"
            (prettyAssertEqual ""
                simpleMetaModule
                (liftModule simpleKoreModule)
            )
        , testCase "Lift Definition"
            (prettyAssertEqual ""
                simpleMetaDefinition
                (liftDefinition simpleKoreDefinition)
            )
        ]

testLiftUnlift
    :: ( LiftableToMetaML a
       , UnliftableFromMetaML a
       , Eq a
       , Show a
       , PrettyPrint a
       , HasCallStack
       )
    => String
    -> CommonMetaPattern
    -> a
    -> TestTree
testLiftUnlift message metaPattern mixed =
    testGroup message
        [ testCase "Lifting"
            (prettyAssertEqual "" metaPattern (liftToMeta mixed))
        , testCase "Unlifting"
            (prettyAssertEqual ""
                (Just mixed)
                (unliftFromMeta metaPattern)
            )
        ]

prettyAssertEqual
    :: (Eq a, PrettyPrint a, HasCallStack)
    => String -- ^ The message prefix
    -> a      -- ^ The expected value
    -> a      -- ^ The actual value
    -> IO ()
prettyAssertEqual = assertEqualWithPrinter prettyPrintToString


natSort :: Sort Object
natSort = SortActualSort SortActual
    { sortActualName = Id "Nat"
    , sortActualSorts = []
    }

stringPattern :: Pattern Meta Variable child
stringPattern = StringLiteralPattern (StringLiteral "a")

unifiedStringPattern :: CommonKorePattern
unifiedStringPattern = asKorePattern stringPattern

metaStringPattern :: CommonMetaPattern
metaStringPattern = Fix stringPattern

sentenceImport :: SentenceImport pat variable
sentenceImport =
    SentenceImport
        { sentenceImportModuleName = ModuleName "MODULE"
        , sentenceImportAttributes = Attributes []
        }

koreSentenceImport :: KoreSentence
koreSentenceImport = asSentence (sentenceImport :: KoreSentenceImport)

metaSentenceImport :: MetaSentence
metaSentenceImport = SentenceImportSentence sentenceImport

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
