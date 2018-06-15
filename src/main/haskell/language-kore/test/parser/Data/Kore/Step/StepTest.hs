{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Step.StepTest (stepTests) where

import           Test.Tasty                            (TestTree, testGroup)
import           Test.Tasty.HUnit                      (testCase)

import           Data.Kore.AST.Common                  (Application (..),
                                                        AstLocation (..),
                                                        Id (..),
                                                        Pattern (ApplicationPattern),
                                                        SymbolOrAlias (..),
                                                        Variable)
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureToKore              (patternKoreToPure)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Comparators                 ()
import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import           Data.Kore.MetaML.AST                  (CommonMetaPattern)
import           Data.Kore.Step.BaseStep
import           Data.Kore.Step.Step
import           Data.Kore.Unification.Unifier         (FunctionalProof (..),
                                                        UnificationProof (..))
import           Data.Kore.Variables.Fresh.IntCounter

import           Test.Tasty.HUnit.Extensions

v1 :: MetaSort sort => sort -> MetaVariable sort
v1 = metaVariable "#v1" AstLocationTest
a1 :: MetaSort sort => sort -> MetaVariable sort
a1 = metaVariable "#a1" AstLocationTest
b1 :: MetaSort sort => sort -> MetaVariable sort
b1 = metaVariable "#b1" AstLocationTest
x1 :: MetaSort sort => sort -> MetaVariable sort
x1 = metaVariable "#x1" AstLocationTest
var_0 :: MetaSort sort => sort -> MetaVariable sort
var_0 = metaVariable "#var_0" AstLocationTest
var_1 :: MetaSort sort => sort -> MetaVariable sort
var_1 = metaVariable "#var_1" AstLocationTest
top :: MetaSort sort => sort -> CommonMetaPattern
top sort = asPureMetaPattern $ metaTop sort

stepTests :: TestTree
stepTests =
    testGroup
        "Step Tests"
        [ singleStepTests
        , multipleStepPickFirstTests
        ]

singleStepTests :: TestTree
singleStepTests =
    testGroup
        "Single step Tests"
        [ testCase "Applies a simple axiom."
            (assertEqualWithExplanation ""
                [   ( StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (v1 PatternSort)
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition =
                            asPureMetaPattern
                                (metaAnd
                                    SortSort
                                    (metaTop SortSort)
                                    (metaTop SortSort)
                                )
                        }
                    , StepProofCombined
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (x1 PatternSort) (var_0 PatternSort)
                            ]
                        , StepProofUnification
                            ( proposition_5_24_3
                                [ functionalVariable (v1 PatternSort) ]
                                (var_0 PatternSort)
                                (v1 PatternSort)
                            )
                        ]
                    )
                ]
                (runStep
                    mockMetadataTools
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (v1 PatternSort)
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                        , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                        }
                    ]
                )
            )
        , testCase "Applies two simple axioms."
            (assertEqualWithExplanation ""
                [   ( StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (v1 PatternSort)
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition =
                            asPureMetaPattern
                                (metaAnd
                                    SortSort
                                    (metaTop SortSort)
                                    (metaTop SortSort)
                                )
                        }
                    , StepProofCombined
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (x1 PatternSort) (var_0 PatternSort)
                            ]
                        , StepProofUnification
                            ( proposition_5_24_3
                                [ functionalVariable (v1 PatternSort) ]
                                (var_0 PatternSort)
                                (v1 PatternSort)
                            )
                        ]
                    )
                ,   ( StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern
                                (metaAnd PatternSort
                                    (v1 PatternSort)
                                    (v1 PatternSort)
                                )
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition =
                            asPureMetaPattern
                                (metaAnd
                                    SortSort
                                    (metaTop SortSort)
                                    (metaTop SortSort)
                                )
                        }
                    , StepProofCombined
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (x1 PatternSort) (var_1 PatternSort)
                            ]
                        , StepProofUnification
                            ( proposition_5_24_3
                                [ functionalVariable (v1 PatternSort) ]
                                (var_1 PatternSort)
                                (v1 PatternSort)
                            )
                        ]
                    )
                ]
                (runStep
                    mockMetadataTools
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (v1 PatternSort)
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                        , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                        }
                    , AxiomPattern
                        { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                        , axiomPatternRight =
                            asPureMetaPattern
                                (metaAnd PatternSort
                                    (x1 PatternSort)
                                    (x1 PatternSort)
                                )
                        }
                    ]
                )
            )
        , testCase "Fails to apply a simple axiom."
            (assertEqualWithExplanation ""
                []
                (runStep
                    mockMetadataTools
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern
                                ( metaSigma
                                    (metaG (a1 PatternSort))
                                    (metaF (b1 PatternSort))
                                )
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern
                                (metaSigma (x1 PatternSort) (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (x1 PatternSort)
                        }
                    ]
                )
            )
        ]

multipleStepPickFirstTests :: TestTree
multipleStepPickFirstTests =
    testGroup
        "Pick-first stepper Tests"
        [ testCase "Runs one step."
            (assertEqualWithExplanation ""
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (metaG (v1 PatternSort))
                    , stepperConfigurationConditionSort = asAst SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern
                            (metaAnd
                                SortSort
                                (metaTop SortSort)
                                (metaTop SortSort)
                            )
                    }
                , StepProofCombined
                    [ StepProofCombined
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (x1 PatternSort) (var_0 PatternSort)
                            ]
                        , StepProofUnification
                            (AndDistributionAndConstraintLifting
                                fSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (v1 PatternSort) ]
                                    (var_0 PatternSort)
                                    (v1 PatternSort)
                                ]
                            )
                        ]
                    , StepProofCombined []
                    ]
                )
                (runStepsPickFirst
                    mockMetadataTools
                    AnyStepCount
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (metaF (v1 PatternSort))
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaF (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        }
                    ]
                )
            )
        , testCase "Runs two steps."
            (assertEqualWithExplanation ""
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (metaH (v1 PatternSort))
                    , stepperConfigurationConditionSort = asAst SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern
                            (metaAnd
                                SortSort
                                (metaAnd
                                    SortSort
                                    (metaTop SortSort)
                                    (metaTop SortSort)
                                )
                                (metaTop SortSort)
                            )
                    }
                , StepProofCombined
                    [ StepProofCombined
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (x1 PatternSort) (var_0 PatternSort)
                            ]
                        , StepProofUnification
                            (AndDistributionAndConstraintLifting
                                fSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (v1 PatternSort) ]
                                    (var_0 PatternSort)
                                    (v1 PatternSort)
                                ]
                            )
                        ]
                    , StepProofCombined
                        [ StepProofCombined
                            [ StepProofVariableRenamings
                                [ variableRenaming
                                    (x1 PatternSort) (var_1 PatternSort)
                                ]
                            , StepProofUnification
                                (AndDistributionAndConstraintLifting
                                    gSymbol
                                    [ proposition_5_24_3
                                        [ functionalVariable (v1 PatternSort) ]
                                        (var_1 PatternSort)
                                        (v1 PatternSort)
                                    ]
                                )
                            ]
                        , StepProofCombined []
                        ]
                    ]
                )
                (runStepsPickFirst
                    mockMetadataTools
                    AnyStepCount
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (metaF (v1 PatternSort))
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaF (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        }
                    , AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaH (x1 PatternSort))
                        }
                    ]
                )
            )
        , testCase "Obeys step limit."
            (assertEqualWithExplanation ""
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (metaG (v1 PatternSort))
                    , stepperConfigurationConditionSort = asAst SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern
                            (metaAnd
                                SortSort
                                (metaTop SortSort)
                                (metaTop SortSort)
                            )
                    }
                , StepProofCombined
                    [ StepProofCombined
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (x1 PatternSort) (var_0 PatternSort)
                            ]
                        , StepProofUnification
                            (AndDistributionAndConstraintLifting
                                fSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (v1 PatternSort) ]
                                    (var_0 PatternSort)
                                    (v1 PatternSort)
                                ]
                            )
                        ]
                    , StepProofCombined []
                    ]
                )
                (runStepsPickFirst
                    mockMetadataTools
                    (MaxStepCount 1)
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (metaF (v1 PatternSort))
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaF (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        }
                    , AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaH (x1 PatternSort))
                        }
                    ]
                )
            )
        , testCase "0 step limit."
            (assertEqualWithExplanation ""
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (metaF (v1 PatternSort))
                    , stepperConfigurationConditionSort = asAst SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern (metaTop SortSort)
                    }
                , StepProofCombined []
                )
                (runStepsPickFirst
                    mockMetadataTools
                    (MaxStepCount 0)
                    StepperConfiguration
                        { stepperConfigurationPattern =
                            asPureMetaPattern (metaF (v1 PatternSort))
                        , stepperConfigurationConditionSort = asAst SortSort
                        , stepperConfigurationCondition = top SortSort
                        }
                    [ AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaF (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        }
                    , AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern (metaG (x1 PatternSort))
                        , axiomPatternRight =
                            asPureMetaPattern (metaH (x1 PatternSort))
                        }
                    ]
                )
            )
        ]

mockMetadataTools :: MetadataTools Meta
mockMetadataTools = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , getArgumentSorts = const [asAst PatternSort, asAst PatternSort]
    , getResultSort = const (asAst PatternSort)
    }


sigmaSymbol :: SymbolOrAlias Meta
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#sigma" AstLocationTest
    , symbolOrAliasParams = []
    }

data MetaSigma p1 p2 = MetaSigma p1 p2
instance (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => ProperPattern Meta PatternSort (MetaSigma p1 p2)
  where
    asProperPattern (MetaSigma p1 p2) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = sigmaSymbol
            , applicationChildren = [asAst p1, asAst p2]
            }
metaSigma
    :: (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => p1 -> p2 -> MetaSigma p1 p2
metaSigma = MetaSigma


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#f" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaF p1 = MetaF p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaF p1)
  where
    asProperPattern (MetaF p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = fSymbol
            , applicationChildren = [asAst p1]
            }
metaF
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaF p1
metaF = MetaF


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#g" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaG p1 = MetaG p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaG p1)
  where
    asProperPattern (MetaG p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = gSymbol
            , applicationChildren = [asAst p1]
            }
metaG
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaG p1
metaG = MetaG


hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#h" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaH p1 = MetaH p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaH p1)
  where
    asProperPattern (MetaH p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = hSymbol
            , applicationChildren = [asAst p1]
            }
metaH
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaH p1
metaH = MetaH

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
asPureMetaPattern patt = patternKoreToPure Meta (asAst patt)

variableRenaming
    :: MetaSort sort
    => MetaVariable sort -> MetaVariable sort -> VariableRenaming Meta
variableRenaming from to =
    VariableRenaming
        { variableRenamingOriginal = AxiomVariable (asMetaVariable from)
        , variableRenamingRenamed =
            ConfigurationVariable (asMetaVariable to)
        }

proposition_5_24_3
    :: (MetaSort sort1, ProperPattern Meta sort2 patt)
    => [FunctionalProof Meta Variable]
    -> MetaVariable sort1
    -> patt
    -> UnificationProof Meta Variable
proposition_5_24_3 functionalProof variable patt =
    Proposition_5_24_3
        functionalProof
        (asMetaVariable variable)
        (asPureMetaPattern patt)

functionalVariable
    :: MetaSort sort => MetaVariable sort -> FunctionalProof Meta Variable
functionalVariable = FunctionalVariable . asMetaVariable

runStep
    :: MetaOrObject level
    => MetadataTools level
    -- ^functions yielding metadata for pattern heads
    -> StepperConfiguration level
    -- ^left-hand-side of unification
    -> [AxiomPattern level]
    -> [(StepperConfiguration level, StepProof level)]
runStep metadataTools configuration axioms =
    fst $ runIntCounter (sequence (step metadataTools configuration axioms)) 0


runStepsPickFirst
    :: MetaOrObject level
    => MetadataTools level
    -- ^functions yielding metadata for pattern heads
    -> MaxStepCount
    -> StepperConfiguration level
    -- ^left-hand-side of unification
    -> [AxiomPattern level]
    -> (StepperConfiguration level, StepProof level)
runStepsPickFirst metadataTools maxStepCount configuration axioms =
    fst $
        runIntCounter
            (pickFirstStepper metadataTools maxStepCount configuration axioms)
            0
