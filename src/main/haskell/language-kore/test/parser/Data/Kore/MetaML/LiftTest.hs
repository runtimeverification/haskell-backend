module Data.Kore.MetaML.LiftTest where

import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (assertEqual, testCase)

import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.MetaML.Lift

liftTests :: TestTree
liftTests =
    testGroup
        "Lifting Tests"
        [ testCase "Lifting an Id"
            (assertEqual ""
                (Fix (StringLiteralPattern (StringLiteral "object")))
                (liftToMeta (Id "object" :: Id Object))
            )
        , testCase "Lifting an actual sort"
            (assertEqual ""
                (Fix
                    (ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = Id "#consSortList"
                            , symbolOrAliasParams = []
                            }
                        , applicationChildren=
                            [ Fix
                                 (ApplicationPattern Application
                                     { applicationSymbolOrAlias = SymbolOrAlias
                                         { symbolOrAliasConstructor = Id "#`Exp"
                                         , symbolOrAliasParams = []
                                         }
                                     , applicationChildren =
                                         [ Fix
                                             (VariablePattern Variable
                                                 { variableName = Id "#v"
                                                 , variableSort =
                                                     SortActualSort SortActual
                                                         { sortActualName = Id "#Sort"
                                                         , sortActualSorts = []
                                                         }
                                                 }
                                             )
                                         ]
                                     }
                                 )
                            , Fix
                                (ApplicationPattern Application
                                    { applicationSymbolOrAlias = SymbolOrAlias
                                        { symbolOrAliasConstructor = Id "#nilSortList"
                                        , symbolOrAliasParams = []
                                        }
                                    , applicationChildren = []
                                    }
                                )
                            ]
                        }
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
                    (ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = Id "#consPatternList"
                            , symbolOrAliasParams = []
                            }
                        , applicationChildren =
                            [ Fix
                                (ApplicationPattern Application
                                    { applicationSymbolOrAlias = SymbolOrAlias
                                        { symbolOrAliasConstructor =
                                            Id "#variable"
                                        , symbolOrAliasParams = []
                                        }
                                    , applicationChildren =
                                        [ Fix
                                            (StringLiteralPattern
                                                (StringLiteral "object")
                                            )
                                        , Fix
                                            (VariablePattern Variable
                                                { variableName = Id "#v"
                                                , variableSort =
                                                    SortActualSort SortActual
                                                    { sortActualName =
                                                        Id "#Sort"
                                                    , sortActualSorts = []
                                                    }
                                                }
                                            )
                                        ]
                                    }
                                )
                            , Fix
                                (ApplicationPattern Application
                                    { applicationSymbolOrAlias = SymbolOrAlias
                                        { symbolOrAliasConstructor =
                                            Id "#nilPatternList"
                                        , symbolOrAliasParams = []
                                        }
                                    , applicationChildren = []
                                    }
                                )
                            ]
                        }
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
        , testCase "Lifting Meta pattern"
            (assertEqual ""
                (Fix (StringLiteralPattern (StringLiteral "object")))
                (liftToMeta (Id "object" :: Id Object))
            )
        , testCase "Testing lifting a pure object pattern."
            (assertEqual ""
                ( Fix
                    ( ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = Id "#\\not"
                            , symbolOrAliasParams = []
                            }
                        , applicationChildren =
                            [ Fix
                                ( VariablePattern Variable
                                    { variableName = Id "#a"
                                    , variableSort = SortActualSort SortActual
                                        { sortActualName = Id "#Sort"
                                        , sortActualSorts = []
                                        }
                                    }
                                )
                            , Fix
                                ( ApplicationPattern Application
                                    { applicationSymbolOrAlias = SymbolOrAlias
                                        { symbolOrAliasConstructor = Id "#\\top"
                                        , symbolOrAliasParams = []
                                        }
                                    , applicationChildren =
                                        [ Fix
                                            ( VariablePattern Variable
                                                { variableName = Id "#a"
                                                , variableSort =
                                                    SortActualSort SortActual
                                                        { sortActualName =
                                                            Id "#Sort"
                                                        , sortActualSorts = []
                                                        }
                                                }
                                            )
                                        ]
                                    }
                                )
                            ]
                        }
                    )
                )
                ( liftToMeta
                    ( ObjectPattern
                        ( NotPattern Not
                            { notSort = SortVariableSort
                                (SortVariable (Id "a"))
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
        ]
