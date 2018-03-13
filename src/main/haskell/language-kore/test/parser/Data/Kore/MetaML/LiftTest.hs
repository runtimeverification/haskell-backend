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
        [ testCase "Testing lifting a pure object pattern."
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
