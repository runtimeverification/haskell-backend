module Test.Kore.Step.BaseStep (test_baseStep) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Test.Tasty.HUnit.Extensions

import Kore.AST.Common
       ( Application (..), AstLocation (..), Id (..),
       Pattern (ApplicationPattern), Sort, SymbolOrAlias (..), Variable )
import Kore.AST.MetaOrObject
import Kore.AST.PureToKore
       ( patternKoreToPure )
import Kore.Building.AsAst
import Kore.Building.Patterns
import Kore.Building.Sorts
import Kore.Error
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..) )
import Kore.MetaML.AST
       ( CommonMetaPattern )
import Kore.Step.BaseStep
import Kore.Step.Condition.Condition
       ( ConditionSort (..) )
import Kore.Step.Error
import Kore.Unification.Error
import Kore.Unification.Unifier
       ( FunctionalProof (..), UnificationProof (..) )
import Kore.Variables.Fresh.IntCounter

import Test.Kore.Comparators ()

test_baseStep :: [TestTree]
test_baseStep =
    [ testCase "Substituting a variable."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (v1 PatternSort)
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
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
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (v1 PatternSort)
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    }
            )
        )
    , testCase "Substituting a variable with a larger one."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (y1 PatternSort)
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
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
                            [ functionalVariable (y1 PatternSort) ]
                            (var_0 PatternSort)
                            (y1 PatternSort)
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (y1 PatternSort)
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    }
            )
        )
    , testCase "Substituting a variable with itself."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (v1 PatternSort)
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
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
                        ( CombinedUnificationProof
                            [ AndDistributionAndConstraintLifting
                                sigmaSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (v1 PatternSort) ]
                                    (var_0 PatternSort)
                                    (v1 PatternSort)
                                , proposition_5_24_3
                                    [ functionalVariable (v1 PatternSort) ]
                                    (var_0 PatternSort)
                                    (v1 PatternSort)
                                ]
                            , ConjunctionIdempotency
                                (asPureMetaPattern (v1 PatternSort))
                            ]
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaSigma (v1 PatternSort) (v1 PatternSort))
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(a, f(b))
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Merging configuration patterns."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaF (b1 PatternSort))
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern
                            (metaAnd
                                SortSort
                                (metaTop SortSort)
                                (metaEquals
                                    (ResultSort SortSort)
                                    PatternSort
                                    (a1 PatternSort)
                                    (metaF (b1 PatternSort))
                                )
                            )
                    }
                , StepProofCombined
                    [ StepProofVariableRenamings
                        [ variableRenaming
                            (x1 PatternSort) (var_0 PatternSort)
                        ]
                    , StepProofUnification
                        ( CombinedUnificationProof
                            [ AndDistributionAndConstraintLifting
                                sigmaSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (a1 PatternSort) ]
                                    (var_0 PatternSort)
                                    (a1 PatternSort)
                                , proposition_5_24_3
                                    [ FunctionalHead fSymbol
                                    , functionalVariable (b1 PatternSort)
                                    ]
                                    (var_0 PatternSort)
                                    (metaF (b1 PatternSort))
                                ]
                            , proposition_5_24_3
                                [ FunctionalHead fSymbol
                                , functionalVariable (b1 PatternSort)
                                ]
                                (a1 PatternSort)
                                (metaF (b1 PatternSort))
                            ]
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaSigma
                                (a1 PatternSort)
                                (metaF (b1 PatternSort))
                            )
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(f(a), f(b))
    -- Expected: f(b) and a=b
    , testCase "Substitution with symbol matching."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaF (b1 PatternSort))
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern
                            (metaAnd
                                SortSort
                                (metaTop SortSort)
                                (metaEquals
                                    (ResultSort SortSort)
                                    PatternSort
                                    (a1 PatternSort)
                                    (b1 PatternSort)
                                )
                            )
                    }
                , StepProofCombined
                    [ StepProofVariableRenamings
                        [ variableRenaming
                            (x1 PatternSort) (var_0 PatternSort)
                        ]
                    , StepProofUnification
                        ( CombinedUnificationProof
                            [ AndDistributionAndConstraintLifting
                                sigmaSymbol
                                [ proposition_5_24_3
                                    [ FunctionalHead fSymbol
                                    , functionalVariable (a1 PatternSort)
                                    ]
                                    (var_0 PatternSort)
                                    (metaF (a1 PatternSort))
                                , proposition_5_24_3
                                    [ FunctionalHead fSymbol
                                    , functionalVariable (b1 PatternSort)
                                    ]
                                    (var_0 PatternSort)
                                    (metaF (b1 PatternSort))
                                ]
                            , AndDistributionAndConstraintLifting
                                fSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (b1 PatternSort)
                                    ]
                                    (a1 PatternSort)
                                    (b1 PatternSort)
                                ]
                            ]
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaSigma
                                (metaF (a1 PatternSort))
                                (metaF (b1 PatternSort))
                            )
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(y, y)
    -- Expected: y
    , testCase "Identical variables have no condition, alphabetical larger."
        (identicalVariablesAssertion y1)
    -- sigma(x, x) => x   vs   sigma(a, a)
    -- Expected: a
    , testCase "Identical variables have no condition, alphabetical lower."
        (identicalVariablesAssertion a1)

    -- sigma(sigma(x, x), sigma(y, y)) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, b), sigma(b, a))
    -- Expected: sigma(b, b) and a=b
    , testCase "Merge multiple variables."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaSigma (b1 PatternSort) (b1 PatternSort))
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition =
                        asPureMetaPattern
                            (metaAnd
                                SortSort
                                (metaTop SortSort)
                                (metaEquals
                                    (ResultSort SortSort)
                                    PatternSort
                                    (a1 PatternSort)
                                    (b1 PatternSort)
                                )
                            )
                    }
                , StepProofCombined
                    [ StepProofVariableRenamings
                        [ variableRenaming
                            (x1 PatternSort) (var_0 PatternSort)
                        , variableRenaming
                            (y1 PatternSort) (var_1 PatternSort)
                        ]
                    , StepProofUnification
                        ( CombinedUnificationProof
                            [ AndDistributionAndConstraintLifting
                                sigmaSymbol
                                [ AndDistributionAndConstraintLifting
                                    sigmaSymbol
                                    [ proposition_5_24_3
                                        [ functionalVariable (a1 PatternSort)
                                        ]
                                        (var_0 PatternSort)
                                        (a1 PatternSort)
                                    , proposition_5_24_3
                                        [ functionalVariable (b1 PatternSort)
                                        ]
                                        (var_0 PatternSort)
                                        (b1 PatternSort)
                                    ]
                                , AndDistributionAndConstraintLifting
                                    sigmaSymbol
                                    [ proposition_5_24_3
                                        [ functionalVariable (b1 PatternSort)
                                        ]
                                        (var_1 PatternSort)
                                        (b1 PatternSort)
                                    , proposition_5_24_3
                                        [ functionalVariable (a1 PatternSort)
                                        ]
                                        (var_1 PatternSort)
                                        (a1 PatternSort)
                                    ]
                                ]
                            , proposition_5_24_3
                                [ functionalVariable (b1 PatternSort)
                                ]
                                (a1 PatternSort)
                                (b1 PatternSort)
                            , proposition_5_24_3
                                [ functionalVariable (a1 PatternSort)
                                ]
                                (b1 PatternSort)
                                (a1 PatternSort)
                            , ConjunctionIdempotency
                                (asPureMetaPattern (b1 PatternSort))
                            ]
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaSigma
                                (metaSigma
                                    (a1 PatternSort)
                                    (b1 PatternSort)
                                )
                                (metaSigma
                                    (b1 PatternSort)
                                    (a1 PatternSort)
                                )
                            )
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma
                                (metaSigma
                                    (x1 PatternSort) (x1 PatternSort)
                                )
                                (metaSigma
                                    (y1 PatternSort) (y1 PatternSort)
                                )
                            )
                    , axiomPatternRight =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (y1 PatternSort))
                    }
            )
        )
    -- x => exists a . x    vs    a
    -- Expected: exists <newvar> . a
    , testCase "Rename quantified rhs variables."
        (assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaExists
                                PatternSort
                                (var_0 PatternSort)
                                (a1 PatternSort)
                            )
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
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
                            (a1 PatternSort) (var_0 PatternSort)
                        , variableRenaming
                            (x1 PatternSort) (var_1 PatternSort)
                        ]
                    , StepProofUnification
                        ( proposition_5_24_3
                            [ functionalVariable (a1 PatternSort)
                            ]
                            (var_1 PatternSort)
                            (a1 PatternSort)
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (a1 PatternSort)
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight =
                        asPureMetaPattern
                            (metaExists
                                PatternSort
                                (a1 PatternSort)
                                (x1 PatternSort)
                            )
                    }
            )
        )
    -- sigma(x, x) -> x   vs   sigma(g(a), f(b))
    -- Expected: error because g(a) != f(b)
    , testCase "Symbol clashes."
        (assertEqualWithExplanation ""
            (Left $ StepErrorUnification $ ConstructorClash gSymbol fSymbol)
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            ( metaSigma
                                (metaG (a1 PatternSort))
                                (metaF (b1 PatternSort))
                            )
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (x1 PatternSort)
                    }
            )
        )
    -- sigma(sigma(x, x), sigma(y, y)) -> sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), sigma(b, a))
    -- Expected: Error because a=f(b) and b=a.
    , testCase "Impossible substitution."
        (assertEqualWithExplanation ""
            (Left $ StepErrorSubstitution
                (CircularVariableDependency
                    [ asMetaVariable (b1 PatternSort) ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            ( metaSigma
                                (metaSigma
                                    (a1 PatternSort)
                                    (metaF (b1 PatternSort))
                                )
                                (metaSigma
                                    (a1 PatternSort) (b1 PatternSort)
                                )
                            )
                    , stepperConfigurationConditionSort =
                        conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma
                                (metaSigma
                                    (x1 PatternSort) (x1 PatternSort)
                                )
                                (metaSigma
                                    (y1 PatternSort) (y1 PatternSort)
                                )
                            )
                        , axiomPatternRight =
                            asPureMetaPattern
                                (metaSigma
                                    (x1 PatternSort) (y1 PatternSort)
                                )
                    }
            )
        )

    -- TODO(virgil): add tests for these after we implement
    -- a => sigma(x, y) substitutions where a is a configuration variable
    -- and x, y are axiom variables.

    -- sigma(x, y) => y    vs    a
    -- sigma(x, sigma(y, z)) => sigma(x, sigma(y, z))    vs    sigma(y, a)
    ]
  where
    v1 :: MetaSort sort => sort -> MetaVariable sort
    v1 = metaVariable "#v1" AstLocationTest
    a1 :: MetaSort sort => sort -> MetaVariable sort
    a1 = metaVariable "#a1" AstLocationTest
    b1 :: MetaSort sort => sort -> MetaVariable sort
    b1 = metaVariable "#b1" AstLocationTest
    x1 :: MetaSort sort => sort -> MetaVariable sort
    x1 = metaVariable "#x1" AstLocationTest
    y1 :: MetaSort sort => sort -> MetaVariable sort
    y1 = metaVariable "#y1" AstLocationTest
    var_0 :: MetaSort sort => sort -> MetaVariable sort
    var_0 = metaVariable "#var_0" AstLocationTest
    var_1 :: MetaSort sort => sort -> MetaVariable sort
    var_1 = metaVariable "#var_1" AstLocationTest
    top :: MetaSort sort => sort -> CommonMetaPattern
    top sort = asPureMetaPattern $ metaTop sort
    variableRenaming
        :: MetaSort sort
        => MetaVariable sort -> MetaVariable sort -> VariableRenaming Meta
    variableRenaming from to =
        VariableRenaming
            { variableRenamingOriginal = AxiomVariable (asMetaVariable from)
            , variableRenamingRenamed =
                ConfigurationVariable (asMetaVariable to)
            }
    asPureMetaPattern
        :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
    asPureMetaPattern patt =
        case patternKoreToPure Meta (asAst patt) of
            Left err  -> error (printError err)
            Right pat -> pat
    functionalVariable
        :: MetaSort sort => MetaVariable sort -> FunctionalProof Meta Variable
    functionalVariable = FunctionalVariable . asMetaVariable
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
    identicalVariablesAssertion var =
        assertEqualWithExplanation ""
            (Right
                ( StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern (var PatternSort)
                    , stepperConfigurationConditionSort = conditionSort SortSort
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
                        ( CombinedUnificationProof
                            [ AndDistributionAndConstraintLifting
                                sigmaSymbol
                                [ proposition_5_24_3
                                    [ functionalVariable (var PatternSort)
                                    ]
                                    (var_0 PatternSort)
                                    (var PatternSort)
                                , proposition_5_24_3
                                    [ functionalVariable (var PatternSort)
                                    ]
                                    (var_0 PatternSort)
                                    (var PatternSort)
                                ]
                            , ConjunctionIdempotency
                                (asPureMetaPattern (var PatternSort))
                            ]
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                StepperConfiguration
                    { stepperConfigurationPattern =
                        asPureMetaPattern
                            (metaSigma
                                (var PatternSort)
                                (var PatternSort)
                            )
                    , stepperConfigurationConditionSort = conditionSort SortSort
                    , stepperConfigurationCondition = top SortSort
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    }
            )

conditionSort :: AsAst (Sort level) s => s -> ConditionSort level
conditionSort sort = ConditionSort (asAst sort)

mockMetadataTools :: MetadataTools Meta
mockMetadataTools = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , isFunction = const False
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


runStep
    :: MetaOrObject level
    => MetadataTools level
    -- ^functions yielding metadata for pattern heads
    -> StepperConfiguration level
    -- ^left-hand-side of unification
    -> AxiomPattern level
    -> Either
        (StepError level Variable)
        (StepperConfiguration level, StepProof level)
runStep metadataTools configuration axiom =
    case stepWithAxiom metadataTools configuration axiom of
        Left err            -> Left (fst (runIntCounter err 0))
        Right counterResult -> Right (fst (runIntCounter counterResult 0))
