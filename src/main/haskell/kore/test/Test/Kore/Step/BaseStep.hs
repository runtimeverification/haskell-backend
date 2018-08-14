module Test.Kore.Step.BaseStep (test_baseStep) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Default
       ( def )
import Data.Reflection
       ( give )

import Kore.AST.Common
       ( Application (..), AstLocation (..), Id (..),
       Pattern (ApplicationPattern), SymbolOrAlias (..), Variable )
import Kore.AST.MetaOrObject
import Kore.AST.PureToKore
       ( patternKoreToPure )
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.ASTUtils.SmartConstructors
       ( mkBottom )
import Kore.Building.AsAst
import Kore.Building.Patterns
import Kore.Building.Sorts
import Kore.Error
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..), SortTools )
import Kore.MetaML.AST
       ( CommonMetaPattern )
import Kore.Predicate.Predicate
       ( CommonPredicate, makeEqualsPredicate, makeFalsePredicate,
       makeTruePredicate )
import Kore.Step.BaseStep
import Kore.Step.Error
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( ExpandedPattern (..) )
import Kore.Step.ExpandedPattern
       ( CommonExpandedPattern )
import Kore.Step.StepperAttributes
import Kore.Unification.Error
       ( SubstitutionError (..) )
import Kore.Unification.Unifier
       ( FunctionalProof (..), UnificationProof (..) )
import Kore.Variables.Fresh.IntCounter

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_baseStep :: [TestTree]
test_baseStep =
    [ testCase "Substituting a variable."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term = asPureMetaPattern (v1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
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
                ExpandedPattern
                    { term = asPureMetaPattern (v1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    , testCase "Substituting a variable with a larger one."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term = asPureMetaPattern (y1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
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
                ExpandedPattern
                    { term = asPureMetaPattern (y1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    , testCase "Substituting a variable with itself."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term = asPureMetaPattern (v1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
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
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma (v1 PatternSort) (v1 PatternSort))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(a, f(b))
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Merging configuration patterns."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaF (b1 PatternSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( asVariable (a1 PatternSort)
                            , asPureMetaPattern (metaF (b1 PatternSort))
                            )
                        ]
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
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma
                                (a1 PatternSort)
                                (metaF (b1 PatternSort))
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(f(a), f(b))
    -- Expected: f(b) and a=b
    , testCase "Substitution with symbol matching."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term = asPureMetaPattern (metaF (b1 PatternSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( asVariable (a1 PatternSort)
                            , asPureMetaPattern (b1 PatternSort)
                            )
                        ]
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
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma
                                (metaF (a1 PatternSort))
                                (metaF (b1 PatternSort))
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
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
                ( ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma (b1 PatternSort) (b1 PatternSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( asVariable (a1 PatternSort)
                            , asPureMetaPattern (b1 PatternSort)
                            )
                        ]
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
                ExpandedPattern
                    { term =
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
                    , predicate = makeTruePredicate
                    , substitution = []
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
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- x => exists a . x    vs    a
    -- Expected: exists <newvar> . a
    , testCase "Rename quantified rhs variables."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaExists
                                PatternSort
                                (var_0 PatternSort)
                                (a1 PatternSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
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
                ExpandedPattern
                    { term = asPureMetaPattern (a1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
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
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(x, x) -> x   vs   sigma(g(a), f(b))
    -- Expected: error because g(a) != f(b)
    , testCase "Symbol clashes."
        (assertEqualWithExplanation ""
            (Right ExpandedPattern
                { term = mkBottom
                , predicate = makeFalsePredicate
                , substitution = []
                }
            )
            (fst <$> runStep
                mockMetadataTools
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            ( metaSigma
                                (metaG (a1 PatternSort))
                                (metaF (b1 PatternSort))
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(sigma(x, x), sigma(y, y)) -> sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), sigma(b, a))
    -- Expected: Error because a=f(b) and b=a.
    , testCase "Impossible substitution."
        (assertEqualWithExplanation ""
            (Right ExpandedPattern
                { term = mkBottom
                , predicate = makeFalsePredicate
                , substitution = []
                }
            )
            (fst <$> runStep
                mockMetadataTools
                ExpandedPattern
                    { term =
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
                    , predicate = makeTruePredicate
                    , substitution = []
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
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    -- Expected: Error because a=f(b) and b=a.
    , testCase "Impossible substitution (ctor)."
        (assertEqualWithExplanation ""
            (Right ExpandedPattern
                { term = mkBottom
                , predicate = makeFalsePredicate
                , substitution = []
                }
            )
            (fst <$> runStep
                mockMetadataTools
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma
                                (a1 PatternSort)
                                (metaF (b1 PatternSort))
                            )
                    , predicate = makeTruePredicate
                    , substitution =
                        [
                            ( asMetaVariable (b1 PatternSort)
                            , asPureMetaPattern (a1 PatternSort)
                            )
                        ]
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma
                                (x1 PatternSort) (x1 PatternSort)
                            )
                    , axiomPatternRight =
                        asPureMetaPattern
                            (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    -- Expected: Error because a=h(b) and b=a.
    , testCase "Impossible substitution (non-ctor)."
        (assertEqualWithExplanation ""
            (Left $ StepErrorSubstitution
                (NonCtorCircularVariableDependency
                    [ asMetaVariable (b1 PatternSort) ]
                )
            )
            (fst <$> runStep
                mockMetadataTools
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma
                                (a1 PatternSort)
                                (metaH (b1 PatternSort))
                            )
                    , predicate = makeTruePredicate
                    , substitution =
                        [
                            ( asMetaVariable (b1 PatternSort)
                            , asPureMetaPattern (a1 PatternSort)
                            )
                        ]
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma
                                (x1 PatternSort) (x1 PatternSort)
                            )
                    , axiomPatternRight =
                        asPureMetaPattern
                            (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , let
        fOfB = metaF (b1 PatternSort)
      in
        testCase "Substitution normalization."
            (assertEqualWithExplanation ""
                (Right
                    ( ExpandedPattern
                        { term = asPureMetaPattern (metaSigma fOfB fOfB)
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( asVariable (a1 PatternSort)
                                , asPureMetaPattern fOfB
                                )
                            ]
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
                                            [ FunctionalHead fSymbol
                                            , functionalVariable (b1 PatternSort)
                                            ]
                                            (var_0 PatternSort)
                                            fOfB
                                        ]
                                    , proposition_5_24_3
                                        [ functionalVariable (a1 PatternSort)
                                        ]
                                        (var_1 PatternSort)
                                        (a1 PatternSort)
                                    ]
                                , proposition_5_24_3
                                    [ FunctionalHead fSymbol
                                    , functionalVariable (b1 PatternSort)
                                    ]
                                    (a1 PatternSort)
                                    fOfB
                                ]
                            )
                        ]
                    )
                )
                (runStep
                    mockMetadataTools
                    ExpandedPattern
                        { term =
                            asPureMetaPattern
                                (metaSigma
                                    (metaSigma
                                        (a1 PatternSort)
                                        fOfB
                                    )
                                    (a1 PatternSort)
                                )
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern
                                (metaSigma
                                    (metaSigma
                                        (x1 PatternSort) (x1 PatternSort)
                                    )
                                    (y1 PatternSort)
                                )
                        , axiomPatternRight =
                            asPureMetaPattern
                                (metaSigma (x1 PatternSort) (y1 PatternSort))
                        , axiomPatternRequires = makeTruePredicate
                        }
                )
            )
    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    , let
        fOfB = metaF (b1 PatternSort)
        fOfC= metaF (c1 PatternSort)
      in
        testCase "Merging substitution with existing one."
            (assertEqualWithExplanation ""
                (Right
                    ( ExpandedPattern
                        { term = asPureMetaPattern (metaSigma fOfC fOfC)
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( asVariable (a1 PatternSort)
                                , asPureMetaPattern fOfC
                                )
                            ,   ( asVariable (b1 PatternSort)
                                , asPureMetaPattern (c1 PatternSort)
                                )
                            ]
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
                                            [ FunctionalHead fSymbol
                                            , functionalVariable (b1 PatternSort)
                                            ]
                                            (var_0 PatternSort)
                                            fOfB
                                        ]
                                    , proposition_5_24_3
                                        [ functionalVariable (a1 PatternSort)
                                        ]
                                        (var_1 PatternSort)
                                        (a1 PatternSort)
                                    ]
                                , proposition_5_24_3
                                    [ FunctionalHead fSymbol
                                    , functionalVariable (b1 PatternSort)
                                    ]
                                    (a1 PatternSort)
                                    fOfB
                                ]
                            )
                        ]
                    )
                )
                (runStep
                    mockMetadataTools
                    ExpandedPattern
                        { term =
                            asPureMetaPattern
                                (metaSigma
                                    (metaSigma
                                        (a1 PatternSort)
                                        fOfB
                                    )
                                    (a1 PatternSort)
                                )
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( asVariable (a1 PatternSort)
                                , asPureMetaPattern fOfC
                                )
                            ]
                        }
                    AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern
                                (metaSigma
                                    (metaSigma
                                        (x1 PatternSort) (x1 PatternSort)
                                    )
                                    (y1 PatternSort)
                                )
                        , axiomPatternRight =
                            asPureMetaPattern
                                (metaSigma (x1 PatternSort) (y1 PatternSort))
                        , axiomPatternRequires = makeTruePredicate
                        }
                )
            )
    -- x => x
    -- vs
    -- a and g(a)=f(a)
    -- Expected: y1 and g(a)=f(a)
    , testCase "Preserving initial condition."
        (assertEqualWithExplanation ""
            (Right
                ( ExpandedPattern
                    { term = asPureMetaPattern (a1 PatternSort)
                    , predicate =
                        makeEquals
                            (metaG (a1 PatternSort))
                            (metaF (a1 PatternSort))
                    , substitution = []
                    }
                , StepProofCombined
                    [ StepProofVariableRenamings
                        [ variableRenaming
                            (x1 PatternSort) (var_0 PatternSort)
                        ]
                    , StepProofUnification
                        ( proposition_5_24_3
                            [ functionalVariable (a1 PatternSort) ]
                            (var_0 PatternSort)
                            (a1 PatternSort)
                        )
                    ]
                )
            )
            (runStep
                mockMetadataTools
                ExpandedPattern
                    { term = asPureMetaPattern (a1 PatternSort)
                    , predicate =
                        makeEquals
                            (metaG (a1 PatternSort))
                            (metaF (a1 PatternSort))
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )
        )
    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and g(a)=f(a)
    -- Expected: sigma(f(b), f(b)) and a=f(b) and and g(f(b))=f(f(b))
    , let
        fOfB = metaF (b1 PatternSort)
      in
        testCase "Substitution normalization."
            (assertEqualWithExplanation ""
                (Right
                    ( ExpandedPattern
                        { term = asPureMetaPattern (metaSigma fOfB fOfB)
                        , predicate =
                            makeEquals
                                (metaG fOfB)
                                (metaF fOfB)
                        , substitution =
                            [   ( asVariable (a1 PatternSort)
                                , asPureMetaPattern fOfB
                                )
                            ]
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
                                            [ FunctionalHead fSymbol
                                            , functionalVariable (b1 PatternSort)
                                            ]
                                            (var_0 PatternSort)
                                            fOfB
                                        ]
                                    , proposition_5_24_3
                                        [ functionalVariable (a1 PatternSort)
                                        ]
                                        (var_1 PatternSort)
                                        (a1 PatternSort)
                                    ]
                                , proposition_5_24_3
                                    [ FunctionalHead fSymbol
                                    , functionalVariable (b1 PatternSort)
                                    ]
                                    (a1 PatternSort)
                                    fOfB
                                ]
                            )
                        ]
                    )
                )
                (runStep
                    mockMetadataTools
                    ExpandedPattern
                        { term =
                            asPureMetaPattern
                                (metaSigma
                                    (metaSigma
                                        (a1 PatternSort)
                                        fOfB
                                    )
                                    (a1 PatternSort)
                                )
                        , predicate =
                            makeEquals
                                (metaG (a1 PatternSort))
                                (metaF (a1 PatternSort))
                        , substitution = []
                        }
                    AxiomPattern
                        { axiomPatternLeft =
                            asPureMetaPattern
                                (metaSigma
                                    (metaSigma
                                        (x1 PatternSort) (x1 PatternSort)
                                    )
                                    (y1 PatternSort)
                                )
                        , axiomPatternRight =
                            asPureMetaPattern
                                (metaSigma (x1 PatternSort) (y1 PatternSort))
                        , axiomPatternRequires = makeTruePredicate
                        }
                )
            )
    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , let
          preCondition var =
              makeEquals
                  (metaG (var PatternSort))
                  (metaF (var PatternSort))
      in
        testCase "Conjoins axiom pre-condition"
          (assertEqualWithExplanation ""
              (Right
                  ( ExpandedPattern
                      { term = asPureMetaPattern (a1 PatternSort)
                      , predicate = preCondition a1
                      , substitution = []
                      }
                  , StepProofCombined
                      [ StepProofVariableRenamings
                          [ variableRenaming
                              (x1 PatternSort) (var_0 PatternSort)
                          ]
                      , StepProofUnification
                          ( proposition_5_24_3
                              [ functionalVariable (a1 PatternSort) ]
                              (var_0 PatternSort)
                              (a1 PatternSort)
                          )
                      ]
                  )
              )
              (runStep
                  mockMetadataTools
                  ExpandedPattern
                      { term = asPureMetaPattern (a1 PatternSort)
                      , predicate = makeTruePredicate
                      , substitution = []
                      }
                  AxiomPattern
                      { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                      , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                      , axiomPatternRequires = preCondition x1
                      }
              )
          )

    -- TODO(virgil): add tests for these after we implement
    -- a => sigma(x, y) substitutions where a is a configuration variable
    -- and x, y are axiom variables.

    -- TODO(virgil): Add tests for conditions generated by:
    --           - unification
    --           - merging predicates

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
    c1 :: MetaSort sort => sort -> MetaVariable sort
    c1 = metaVariable "#c1" AstLocationTest
    x1 :: MetaSort sort => sort -> MetaVariable sort
    x1 = metaVariable "#x1" AstLocationTest
    y1 :: MetaSort sort => sort -> MetaVariable sort
    y1 = metaVariable "#y1" AstLocationTest
    var_0 :: MetaSort sort => sort -> MetaVariable sort
    var_0 = metaVariable "#var_0" AstLocationTest
    var_1 :: MetaSort sort => sort -> MetaVariable sort
    var_1 = metaVariable "#var_1" AstLocationTest
    variableRenaming
        :: MetaSort sort
        => MetaVariable sort -> MetaVariable sort -> VariableRenaming Meta
    variableRenaming from to =
        VariableRenaming
            { variableRenamingOriginal = AxiomVariable (asMetaVariable from)
            , variableRenamingRenamed =
                ConfigurationVariable (asMetaVariable to)
            }
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
                ( ExpandedPattern
                    { term =
                        asPureMetaPattern (var PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
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
                ExpandedPattern
                    { term =
                        asPureMetaPattern
                            (metaSigma
                                (var PatternSort)
                                (var PatternSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        asPureMetaPattern
                            (metaSigma (x1 PatternSort) (x1 PatternSort))
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    }
            )

mockStepperAttributes :: SymbolOrAlias Meta -> StepperAttributes
mockStepperAttributes patternHead =
    StepperAttributes
    { isConstructor = patternHead /= hSymbol
    , isFunctional  = True
    , isFunction    = True
    , hook          = def
    }

mockSortTools :: SortTools Meta
mockSortTools = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { attributes = mockStepperAttributes
    , sortTools = mockSortTools
    }

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
asPureMetaPattern patt =
    case patternKoreToPure Meta (asAst patt) of
        Left err -> error (printError err)
        Right p  -> p

makeEquals
    :: (ProperPattern Meta sort patt1, ProperPattern Meta sort patt2)
    => patt1 -> patt2 -> CommonPredicate Meta
makeEquals patt1 patt2 =
    give (sortTools mockMetadataTools)
        (makeEqualsPredicate
            (asPureMetaPattern patt1)
            (asPureMetaPattern patt2)
        )

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

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> AxiomPattern level
    -> Either
        (StepError level Variable)
        (CommonExpandedPattern level, StepProof level)
runStep metadataTools configuration axiom =
    case give metadataTools (stepWithAxiom metadataTools configuration axiom) of
        Left err            -> Left (fst (runIntCounter err 0))
        Right counterResult -> Right (fst (runIntCounter counterResult 0))
