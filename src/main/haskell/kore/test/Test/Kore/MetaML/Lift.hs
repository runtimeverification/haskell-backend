module Test.Kore.MetaML.Lift
    ( prettyAssertEqual, variablePattern
    , test_lift
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( testCase )

import Data.CallStack
import Data.Functor.Foldable

import Kore.AST.Builders
import Kore.AST.BuildersImpl
import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.Sentence
import Kore.ASTPrettyPrint
import Kore.Implicit.ImplicitSorts
import Kore.MetaML.AST
import Kore.MetaML.Lift
import Kore.MetaML.Unlift

import Test.Kore
import Test.Tasty.HUnit.Extensions

variablePattern :: String -> Sort Meta -> CommonMetaPattern
variablePattern name sort =
    fillCheckSort sort (unparameterizedVariable_ name AstLocationTest)

test_lift :: [TestTree]
test_lift =
    [ testLiftUnlift "testId"
        (Fix (StringLiteralPattern (StringLiteral "object")))
        (testId "object" :: Id Object)
    , testLiftUnlift "Meta Pattern"
        metaStringPattern
        unifiedStringPattern
    , testLiftUnlift "Bottom"
        (Fix
            (apply (metaMLPatternHead BottomPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort ]
            )
        )
        (asKorePattern
            ( BottomPattern Bottom
                { bottomSort = SortVariableSort
                    (SortVariable (testId "a" :: Id Object))
                }
            )
        ::CommonKorePattern)
    , testLiftUnlift "Top"
        (Fix
            (apply (metaMLPatternHead TopPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort ]
            )
        )
        (asKorePattern
            ( TopPattern Top
                { topSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                }
            )
        ::CommonKorePattern)
    , testLiftUnlift "Ceil"
        (Fix
            (apply (metaMLPatternHead CeilPatternType AstLocationTest)
                [ variablePattern "#b" sortMetaSort
                , variablePattern "#a" sortMetaSort
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (CeilPattern Ceil
                { ceilResultSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , ceilOperandSort =
                    SortVariableSort (SortVariable (testId "b"))
                , ceilChild = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Floor"
        (Fix
            (apply (metaMLPatternHead FloorPatternType AstLocationTest)
                [ variablePattern "#b" sortMetaSort
                , variablePattern "#a" sortMetaSort
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (FloorPattern Floor
                { floorResultSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , floorOperandSort =
                    SortVariableSort (SortVariable (testId "b"))
                , floorChild = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Equals"
        (Fix
            (apply (metaMLPatternHead EqualsPatternType AstLocationTest)
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
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , equalsOperandSort =
                    SortVariableSort (SortVariable (testId "b"))
                , equalsFirst = unifiedStringPattern
                , equalsSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "In"
        (Fix
            (apply (metaMLPatternHead InPatternType AstLocationTest)
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
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , inOperandSort =
                    SortVariableSort (SortVariable (testId "b"))
                , inContainedChild = unifiedStringPattern
                , inContainingChild = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Forall"
        (Fix
            (apply (metaMLPatternHead ForallPatternType AstLocationTest)
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
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , forallVariable = Variable
                    { variableName = testId "x"
                    , variableSort =
                        SortVariableSort (SortVariable (testId "a"))
                    }
                , forallChild =
                    asKorePattern
                        (VariablePattern Variable
                            { variableName = testId "x" :: Id Object
                            , variableSort = SortVariableSort
                                (SortVariable (testId "a"))
                            }
                        )
                }
            )
        )
    , testLiftUnlift "Exists"
        (Fix
            (apply (metaMLPatternHead ExistsPatternType AstLocationTest)
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
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , existsVariable = Variable
                    { variableName = testId "x"
                    , variableSort =
                        SortVariableSort (SortVariable (testId "a"))
                    }
                , existsChild =
                    asKorePattern
                        (VariablePattern Variable
                            { variableName = testId "x" :: Id Object
                            , variableSort = SortVariableSort
                                (SortVariable (testId "a"))
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
                { variableName = testId "x" :: Id Object
                , variableSort = SortVariableSort
                    (SortVariable (testId "a"))
                }
            )
        )
    , testLiftUnlift "An actual sort"
        (Fix
            (apply consSortListHead
                [ Fix
                    (apply (groundHead "#`Exp" AstLocationTest)
                        [ variablePattern "#v" sortMetaSort ]
                    )
                , Fix (apply nilSortListHead [])
                ]
            )
        )
        [SortActualSort SortActual
            { sortActualName = testId "Exp" :: Id Object
            , sortActualSorts =
                [ SortVariableSort (SortVariable (testId "v")) ]
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
            { variableName = testId "object" :: Id Object
            , variableSort =
                SortVariableSort (SortVariable (testId "v"))
            }
    , testLiftUnlift "A pure object pattern."
        ( Fix
            ( apply (metaMLPatternHead NotPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , Fix
                    ( apply
                        (metaMLPatternHead TopPatternType AstLocationTest)
                        [ variablePattern "#a" sortMetaSort ]
                    )
                ]
            )
        )
        ( asKorePattern
            ( NotPattern Not
                { notSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , notChild = asKorePattern
                    ( TopPattern Top
                        { topSort = SortVariableSort
                            (SortVariable (testId "a" :: Id Object))
                        }
                    )
                }
            )
        ::CommonKorePattern)
    , testLiftUnlift "And pattern"
        (Fix
            (apply (metaMLPatternHead AndPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (AndPattern And
                { andSort =
                    SortVariableSort
                        (SortVariable (testId "a" :: Id Object))
                , andFirst = unifiedStringPattern
                , andSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Or pattern"
        (Fix
            (apply (metaMLPatternHead OrPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (OrPattern Or
                { orSort =
                    SortVariableSort
                        (SortVariable (testId "a" :: Id Object))
                , orFirst = unifiedStringPattern
                , orSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Iff pattern"
        (Fix
            (apply (metaMLPatternHead IffPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (IffPattern Iff
                { iffSort =
                    SortVariableSort
                        (SortVariable (testId "a" :: Id Object))
                , iffFirst = unifiedStringPattern
                , iffSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Implies pattern"
        (Fix
            (apply (metaMLPatternHead ImpliesPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (ImpliesPattern Implies
                { impliesSort =
                    SortVariableSort
                        (SortVariable (testId "a" :: Id Object))
                , impliesFirst = unifiedStringPattern
                , impliesSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Not"
        (Fix
            (apply (metaMLPatternHead NotPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (NotPattern Not
                { notSort =
                    SortVariableSort
                        (SortVariable (testId "a" :: Id Object))
                , notChild = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Rewrites pattern"
        (Fix
            (apply (metaMLPatternHead RewritesPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (RewritesPattern Rewrites
                { rewritesSort =
                    SortVariableSort (SortVariable (testId "a"))
                , rewritesFirst = unifiedStringPattern
                , rewritesSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Domain Value"
        (Fix
            (apply
                (metaMLPatternHead DomainValuePatternType AstLocationTest)
                [ variablePattern "#Int" sortMetaSort
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (DomainValuePattern DomainValue
                { domainValueSort =
                    SortVariableSort (SortVariable (testId "Int"))
                , domainValueChild = metaStringPattern
                }
            )
        :: CommonKorePattern)
    , testLiftUnlift "Application"
        (Fix
            (apply (groundHead "#`test" AstLocationTest)
                [ variablePattern "#Int" sortMetaSort
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (apply
                SymbolOrAlias
                    { symbolOrAliasConstructor = testId "test" :: Id Object
                    , symbolOrAliasParams =
                        [ SortVariableSort (SortVariable (testId "Int"))
                        ]
                    }
                [unifiedStringPattern]
            )
        )
    , testLiftUnlift "Next"
        (Fix
            (apply (metaMLPatternHead NextPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort
                , metaStringPattern
                ]
            )
        )
        (asKorePattern
            (NextPattern Next
                { nextSort =
                    SortVariableSort (SortVariable (testId "a"))
                , nextChild = unifiedStringPattern
                }
            )
        )
    , testCase "Lift Meta Alias Declaration"
        (prettyAssertEqual ""
            [ SentenceAliasSentence SentenceAlias
                { sentenceAliasAlias = Alias
                    { aliasConstructor = testId "#alias"
                    , aliasParams = []
                    }
                , sentenceAliasSorts = []
                , sentenceAliasLeftPattern  = topPatMeta
                , sentenceAliasRightPattern = topPatMeta
                , sentenceAliasResultSort =
                    SortVariableSort (SortVariable (testId "#a"))
                , sentenceAliasAttributes = Attributes []
                }
            ]
            (liftSentence
                (asSentence
                    (SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = testId "#alias"
                            , aliasParams = []
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                                SortVariableSort
                                    (SortVariable (testId "#a"))
                        , sentenceAliasLeftPattern  = topPatMeta
                        , sentenceAliasRightPattern = topPatMeta
                        , sentenceAliasAttributes =
                            Attributes []
                        }
                    :: KoreSentenceAlias Meta)
                )
            )
        )
    , testCase "Lift Object Alias Declaration"
        (prettyAssertEqual ""
            [ SentenceSymbolSentence
                (symbol_ "#`alias" AstLocationTest [] patternMetaSort)
            , SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ sortParameter Meta "#s" AstLocationTest ]
                , sentenceAxiomPattern = Fix
                    (EqualsPattern Equals
                        { equalsOperandSort =
                            SortActualSort SortActual
                                { sortActualName = testId "#Pattern" :: Id Meta
                                , sortActualSorts = []
                                }
                        , equalsResultSort =
                            SortVariableSort
                                (sortParameter Meta "#s" AstLocationTest)
                        , equalsFirst = Fix
                            (apply (groundHead "#\\top" AstLocationImplicit)
                                [ Fix (apply (groundHead "#`s3" AstLocationImplicit) []) ]
                            )
                        , equalsSecond = Fix
                            (apply (groundHead "#\\top" AstLocationImplicit)
                                [ Fix (apply (groundHead "#`s3" AstLocationImplicit) []) ]
                            )
                        })
                , sentenceAxiomAttributes = Attributes []
                }
            ]
            (liftSentence
                (asSentence
                    (SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = testId "alias"
                            , aliasParams = []
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                                SortVariableSort (SortVariable (testId "a"))
                        , sentenceAliasLeftPattern = topPatObj
                        , sentenceAliasRightPattern = topPatObj
                        , sentenceAliasAttributes =
                            Attributes []
                        }
                    :: KoreSentenceAlias Object)
                )
            )
        )
    , testCase "Lift Object Symbol Declaration"
        (prettyAssertEqual ""
            [ SentenceSymbolSentence
                (symbol_ "#`alias" AstLocationTest
                    [sortMetaSort, patternMetaSort]
                    patternMetaSort
                )
            , SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [sortParameter Meta "#s" AstLocationTest]
                , sentenceAxiomPattern =
                    Fix
                        (EqualsPattern Equals
                            { equalsOperandSort = patternMetaSort
                            , equalsResultSort =
                                SortVariableSort
                                    (sortParameter Meta "#s" AstLocationTest)
                            , equalsFirst =
                                Fix
                                    (apply
                                        (groundHead
                                            "#`alias" AstLocationTest)
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
                { sentenceAxiomParameters =
                    [ sortParameter Meta "#s" AstLocationTest ]
                , sentenceAxiomPattern = Fix
                    (ImpliesPattern Implies
                        { impliesSort =
                            SortVariableSort
                                (sortParameter Meta "#s" AstLocationTest)
                        , impliesFirst =
                            Fix
                                (apply
                                    (sortsDeclaredHead
                                        (SortVariableSort
                                            (sortParameter
                                                Meta "#s" AstLocationTest)
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
                                            (sortParameter
                                                Meta "#s" AstLocationTest)
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
                (asSentence
                    (SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = testId "alias"
                            , symbolParams = [SortVariable (testId "a")]
                            }
                        , sentenceSymbolSorts =
                            [ SortVariableSort (SortVariable (testId "a")) ]
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (testId "a"))
                        , sentenceSymbolAttributes =
                            Attributes []
                        }
                    :: KoreSentenceSymbol Object)
                )
            )
        )
    , testCase "Lift Meta Symbol Declaration"
        (prettyAssertEqual ""
            [ SentenceSymbolSentence SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId "#symbol"
                    , symbolParams = []
                    }
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort =
                    SortVariableSort (SortVariable (testId "#a"))
                , sentenceSymbolAttributes = Attributes []
                }
            ]
            (liftSentence
                (asSentence
                    (SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = testId "#symbol"
                            , symbolParams = []
                            }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort =
                                SortVariableSort (SortVariable (testId "#a"))
                        , sentenceSymbolAttributes =
                            Attributes []
                        }
                    :: KoreSentenceSymbol Meta)
                )
            )
        )
    , testCase "Lift Sort Declaration"
        (prettyAssertEqual ""
            [ SentenceSymbolSentence SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId "#`List"
                    , symbolParams = []
                    }
                , sentenceSymbolSorts = [sortMetaSort]
                , sentenceSymbolResultSort = sortMetaSort
                , sentenceSymbolAttributes = Attributes []
                }
            , SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ sortParameter Meta "#s" AstLocationTest ]
                , sentenceAxiomPattern = Fix
                        (EqualsPattern Equals
                            { equalsOperandSort = sortMetaSort
                            , equalsResultSort =
                                SortVariableSort
                                    (sortParameter Meta "#s" AstLocationTest)
                            , equalsFirst = Fix
                                (apply (groundHead "#`List" AstLocationTest)
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
                { sentenceAxiomParameters =
                    [sortParameter Meta "#s" AstLocationTest]
                , sentenceAxiomPattern = Fix
                        (ImpliesPattern Implies
                            { impliesSort =
                                SortVariableSort
                                    (sortParameter
                                        Meta "#s" AstLocationTest)
                            , impliesFirst = Fix
                                (apply
                                    (sortsDeclaredHead
                                        (SortVariableSort
                                            (sortParameter
                                                Meta "#s" AstLocationTest)
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
                                            (sortParameter
                                                Meta "#s" AstLocationTest)
                                        )
                                    )
                                    [ Fix
                                        (apply
                                            (groundHead
                                                "#`List" AstLocationTest)
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
                (asSentence
                    (SentenceSort
                        { sentenceSortName = testId "List"
                        , sentenceSortParameters =
                            [SortVariable (testId "a")]
                        , sentenceSortAttributes =
                            Attributes []
                        }
                    :: KoreSentenceSort Object)
                )
            )
        )
    , testCase "Lift Axiom topped in Object Pattern"
        (prettyAssertEqual ""
            [ SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [sortParameter Meta "#a" AstLocationTest]
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
                                    (apply
                                        (metaMLPatternHead
                                            TopPatternType AstLocationTest)
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
                (constructUnifiedSentence SentenceAxiomSentence $ SentenceAxiom
                    { sentenceAxiomParameters =
                        [ UnifiedObject (SortVariable (testId "a"))
                        , UnifiedMeta (SortVariable (testId "#a"))
                        ]
                    , sentenceAxiomPattern = asKorePattern
                        (TopPattern
                            (Top
                                (SortVariableSort
                                    (SortVariable (testId "a" :: Id Object))
                                )
                            )
                        )
                    , sentenceAxiomAttributes =
                        Attributes [] :: Attributes
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
                        Attributes [] :: Attributes
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
  where
    topPatMeta = TopPattern $ Top { topSort = patternMetaSort }
    topPatObj  = TopPattern $ Top { topSort = simpleSort "s3" }
    simpleSortActual sort =
        SortActual
            { sortActualName = testId sort
            , sortActualSorts = []
            }
    simpleSort sortName = SortActualSort (simpleSortActual sortName)

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
