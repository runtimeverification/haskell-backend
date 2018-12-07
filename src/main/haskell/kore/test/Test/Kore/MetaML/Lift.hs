module Test.Kore.MetaML.Lift
    ( prettyAssertEqual, variablePattern
    , test_lift
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( testCase )

import Data.CallStack
import Data.Proxy
       ( Proxy (..) )
import Data.Text
       ( Text )

import           Kore.AST.Builders
import           Kore.AST.BuildersImpl
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.ASTPrettyPrint
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.Implicit.ImplicitSorts
import           Kore.MetaML.AST
import           Kore.MetaML.Lift
import           Kore.MetaML.Unlift

import Test.Kore
import Test.Tasty.HUnit.Extensions

variablePattern :: Text -> Sort Meta -> CommonMetaPattern
variablePattern name sort =
    fillCheckSort sort (unparameterizedVariable_ name AstLocationTest)

test_lift :: [TestTree]
test_lift =
    [ testLiftUnlift "testId"
        (StringLiteral_ "object")
        (testId "object" :: Id Object)
    , testLiftUnlift "Meta Pattern"
        metaStringPattern
        unifiedStringPattern
    , testLiftUnlift "Bottom"
        (App_
            (metaMLPatternHead BottomPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort ]
        )
        (asCommonKorePattern
            ( BottomPattern Bottom
                { bottomSort = SortVariableSort
                    (SortVariable (testId "a" :: Id Object))
                }
            )
        )
    , testLiftUnlift "Top"
        (App_
            (metaMLPatternHead TopPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort ]
        )
        (asCommonKorePattern
            ( TopPattern Top
                { topSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                }
            )
        )
    , testLiftUnlift "Ceil"
        (App_
            (metaMLPatternHead CeilPatternType AstLocationTest)
            [ variablePattern "#b" sortMetaSort
            , variablePattern "#a" sortMetaSort
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead FloorPatternType AstLocationTest)
            [ variablePattern "#b" sortMetaSort
            , variablePattern "#a" sortMetaSort
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead EqualsPatternType AstLocationTest)
            [ variablePattern "#b" sortMetaSort
            , variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead InPatternType AstLocationTest)
            [ variablePattern "#b" sortMetaSort
            , variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
    , testLiftUnlift @CommonKorePattern "Forall"
        (App_
            (metaMLPatternHead ForallPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , App_
                variableHead
                [ StringLiteral_ "x"
                , variablePattern "#a" sortMetaSort
                ]
            , App_
                variableAsPatternHead
                [ App_
                    variableHead
                    [ StringLiteral_ "x"
                    , variablePattern "#a" sortMetaSort
                    ]
                ]
            ]
        )
        (asCommonKorePattern
            (ForallPattern Forall
                { forallSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , forallVariable = Variable
                    { variableName = testId "x"
                    , variableSort =
                        SortVariableSort (SortVariable (testId "a"))
                    }
                , forallChild =
                    asCommonKorePattern
                        (VariablePattern Variable
                            { variableName = testId "x" :: Id Object
                            , variableSort = SortVariableSort
                                (SortVariable (testId "a"))
                            }
                        )
                }
            )
        )
    , testLiftUnlift @CommonKorePattern "Exists"
        (App_
            (metaMLPatternHead ExistsPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , App_
                variableHead
                [ StringLiteral_ "x"
                , variablePattern "#a" sortMetaSort
                ]
            , App_
                variableAsPatternHead
                [ App_
                    variableHead
                    [ StringLiteral_ "x"
                    , variablePattern "#a" sortMetaSort
                    ]
                ]
            ]
        )
        (asCommonKorePattern
            (ExistsPattern Exists
                { existsSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , existsVariable = Variable
                    { variableName = testId "x"
                    , variableSort =
                        SortVariableSort (SortVariable (testId "a"))
                    }
                , existsChild =
                    asCommonKorePattern
                        (VariablePattern Variable
                            { variableName = testId "x" :: Id Object
                            , variableSort = SortVariableSort
                                (SortVariable (testId "a"))
                            }
                        )
                }
            )
        )
    , testLiftUnlift @CommonKorePattern "Variable Pattern"
        (App_
            variableAsPatternHead
            [ App_
                variableHead
                [ StringLiteral_ "x"
                , variablePattern "#a" sortMetaSort
                ]
            ]
        )
        (asCommonKorePattern
            (VariablePattern Variable
                { variableName = testId "x" :: Id Object
                , variableSort = SortVariableSort
                    (SortVariable (testId "a"))
                }
            )
        )
    , testLiftUnlift "An actual sort"
        (App_
            consSortListHead
            [ App_
                (groundHead "#`Exp" AstLocationTest)
                [ variablePattern "#v" sortMetaSort ]
            , App_ nilSortListHead []
            ]
        )
        [SortActualSort SortActual
            { sortActualName = testId "Exp" :: Id Object
            , sortActualSorts =
                [ SortVariableSort (SortVariable (testId "v")) ]
            }
        ]
    , testLiftUnlift "Meta Pattern List"
        (App_
            consPatternListHead
            [ metaStringPattern
            , App_ nilPatternListHead []
            ]
        )
        [metaStringPattern]
    , testLiftUnlift "A Variable"
        (App_
            variableHead
            [ StringLiteral_ "object"
            , variablePattern "#v" sortMetaSort
            ]
        )
        Variable
            { variableName = testId "object" :: Id Object
            , variableSort =
                SortVariableSort (SortVariable (testId "v"))
            }
    , testLiftUnlift "A pure object pattern."
        (App_
            (metaMLPatternHead NotPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , App_
                (metaMLPatternHead TopPatternType AstLocationTest)
                [ variablePattern "#a" sortMetaSort ]
            ]
        )
        (asCommonKorePattern
            (NotPattern Not
                { notSort =
                    SortVariableSort (SortVariable (testId "a" :: Id Object))
                , notChild = asCommonKorePattern
                    ( TopPattern Top
                        { topSort = SortVariableSort
                            (SortVariable (testId "a" :: Id Object))
                        }
                    )
                }
            )
        )
    , testLiftUnlift "And pattern"
        (App_
            (metaMLPatternHead AndPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead OrPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead IffPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead ImpliesPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
        (App_
            (metaMLPatternHead NotPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
            (NotPattern Not
                { notSort =
                    SortVariableSort
                        (SortVariable (testId "a" :: Id Object))
                , notChild = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Rewrites pattern"
        (App_
            (metaMLPatternHead RewritesPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
            (RewritesPattern Rewrites
                { rewritesSort =
                    SortVariableSort (SortVariable (testId "a"))
                , rewritesFirst = unifiedStringPattern
                , rewritesSecond = unifiedStringPattern
                }
            )
        )
    , testLiftUnlift "Domain Value"
        (App_
            (metaMLPatternHead DomainValuePatternType AstLocationTest)
            [ variablePattern "#Int" sortMetaSort
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
            (DomainValuePattern DomainValue
                { domainValueSort =
                    SortVariableSort (SortVariable (testId "Int"))
                , domainValueChild =
                    Domain.BuiltinPattern
                        (castMetaDomainValues metaStringPattern)
                }
            )
        :: CommonKorePattern)
    , testLiftUnlift "Application"
        (App_
            (groundHead "#`test" AstLocationTest)
            [ variablePattern "#Int" sortMetaSort
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
            (ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId "test" :: Id Object
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable (testId "Int"))
                            ]
                        }
                , applicationChildren = [unifiedStringPattern]
                }
            )
        )
    , testLiftUnlift "Next"
        (App_
            (metaMLPatternHead NextPatternType AstLocationTest)
            [ variablePattern "#a" sortMetaSort
            , metaStringPattern
            ]
        )
        (asCommonKorePattern
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
                    [ sortParameter Proxy "#s" AstLocationTest ]
                , sentenceAxiomPattern =
                    Equals_
                        (SortActualSort SortActual
                            { sortActualName = testId "#Pattern" :: Id Meta
                            , sortActualSorts = []
                            }
                        )
                        (SortVariableSort
                            $ sortParameter Proxy "#s" AstLocationTest)
                        (App_
                            (groundHead "#\\top" AstLocationImplicit)
                            [ App_ (groundHead "#`s3" AstLocationImplicit) [] ]
                        )
                        (App_
                            (groundHead "#\\top" AstLocationImplicit)
                            [ App_ (groundHead "#`s3" AstLocationImplicit) [] ]
                        )
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
                    [sortParameter Proxy "#s" AstLocationTest]
                , sentenceAxiomPattern =
                    Equals_
                        patternMetaSort
                        (SortVariableSort
                            $ sortParameter Proxy "#s" AstLocationTest
                        )
                        (App_
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
                        (App_
                            applicationHead
                            [ App_
                                symbolHead
                                [ StringLiteral_ "alias"
                                , App_
                                    consSortListHead
                                    [ variablePattern "#a" sortMetaSort
                                    , App_ nilSortListHead []
                                    ]
                                , App_
                                    consSortListHead
                                    [ variablePattern "#a" sortMetaSort
                                    , App_ nilSortListHead []
                                    ]
                                , variablePattern "#a" sortMetaSort
                                ]
                            , App_
                                consPatternListHead
                                [ variablePattern "#P1" patternMetaSort
                                , App_ nilPatternListHead []
                                ]
                            ]
                        )
                , sentenceAxiomAttributes = Attributes []
                }
            , SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [ sortParameter Proxy "#s" AstLocationTest ]
                , sentenceAxiomPattern =
                    Implies_
                        (SortVariableSort
                            $ sortParameter Proxy "#s" AstLocationTest
                        )
                        (App_
                            (sortsDeclaredHead
                                $ SortVariableSort
                                $ sortParameter Proxy "#s" AstLocationTest
                            )
                            [ App_
                                consSortListHead
                                [ variablePattern "#a" sortMetaSort
                                , App_ nilSortListHead []
                                ]
                            ]
                        )
                        (App_
                            (symbolDeclaredHead
                                $ SortVariableSort
                                $ sortParameter Proxy "#s" AstLocationTest
                            )
                            [ App_
                                symbolHead
                                [ StringLiteral_ "alias"
                                , App_
                                    consSortListHead
                                    [ variablePattern "#a" sortMetaSort
                                    , App_ nilSortListHead []
                                    ]
                                , App_
                                    consSortListHead
                                    [ variablePattern "#a" sortMetaSort
                                    , App_ nilSortListHead []
                                    ]
                                , variablePattern "#a" sortMetaSort
                                ]
                            ]
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
                    [ sortParameter Proxy "#s" AstLocationTest ]
                , sentenceAxiomPattern =
                    Equals_
                        sortMetaSort
                        (SortVariableSort
                            $ sortParameter Proxy "#s" AstLocationTest
                        )
                        (App_
                            (groundHead "#`List" AstLocationTest)
                            [ variablePattern "#a" sortMetaSort ]
                        )
                        (App_
                            sortHead
                            [ StringLiteral_ "List"
                            , App_
                                consSortListHead
                                [ variablePattern "#a" sortMetaSort
                                , App_ nilSortListHead []
                                ]
                            ]
                        )
                , sentenceAxiomAttributes = Attributes []
                }
            , SentenceAxiomSentence SentenceAxiom
                { sentenceAxiomParameters =
                    [sortParameter Proxy "#s" AstLocationTest]
                , sentenceAxiomPattern =
                    Implies_
                        (SortVariableSort
                            $ sortParameter Proxy "#s" AstLocationTest
                        )
                        (App_
                            (sortsDeclaredHead
                                $ SortVariableSort
                                $ sortParameter Proxy "#s" AstLocationTest
                            )
                            [ App_
                                consSortListHead
                                [ variablePattern "#a" sortMetaSort
                                , App_ nilSortListHead []
                                ]
                            ]
                        )
                        (App_
                            (sortDeclaredHead
                                $ SortVariableSort
                                $ sortParameter Proxy "#s" AstLocationTest
                            )
                            [ App_
                                (groundHead "#`List" AstLocationTest)
                                [ variablePattern "#a" sortMetaSort ]
                            ]
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
                    [sortParameter Proxy "#a" AstLocationTest]
                , sentenceAxiomPattern =
                    Implies_
                        patternMetaSort
                        (App_
                            (sortsDeclaredHead patternMetaSort)
                            [ App_
                                consSortListHead
                                [ variablePattern "#a" sortMetaSort
                                , App_ nilSortListHead []
                                ]
                            ]
                        )
                        (App_
                            (provableHead patternMetaSort)
                            [ App_
                                (metaMLPatternHead
                                    TopPatternType
                                    AstLocationTest
                                )
                                [variablePattern "#a" sortMetaSort]
                            ]
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
                    , sentenceAxiomPattern = asCommonKorePattern
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
                , sentenceAxiomPattern =
                    Implies_
                        charListMetaSort
                        (App_
                            (sortsDeclaredHead charListMetaSort)
                            [ App_ nilSortListHead [] ]
                        )
                        metaStringPattern
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

stringPattern :: Pattern Meta dom Variable child
stringPattern = StringLiteralPattern (StringLiteral "a")

unifiedStringPattern :: CommonKorePattern
unifiedStringPattern = asCommonKorePattern stringPattern

metaStringPattern :: CommonMetaPattern
metaStringPattern = asCommonMetaPattern stringPattern

sentenceImport :: SentenceImport pat dom var
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
