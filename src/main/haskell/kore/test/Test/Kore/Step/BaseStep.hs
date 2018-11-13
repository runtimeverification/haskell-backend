module Test.Kore.Step.BaseStep (test_baseStep) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Control.Monad.Except
                 ( runExceptT )
import           Data.Default
                 ( def )
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( Application (..), AstLocation (..), Id (..),
                 Pattern (ApplicationPattern, StringLiteralPattern),
                 StringLiteral (..), SymbolOrAlias (..), Variable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.Building.AsAst
import           Kore.Building.Patterns
import           Kore.Building.Sorts
import           Kore.Error
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.MetaML.AST
                 ( CommonMetaPattern )
import           Kore.Predicate.Predicate
                 ( CommonPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.BaseStep
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.StepperAttributes
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import           Kore.Unification.Unifier
                 ( UnificationError (..), UnificationProof (..) )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Tasty.HUnit.Extensions

test_baseStep :: [TestTree]
test_baseStep =
    [ testCase "Substituting a variable."
        (assertEqualWithExplanation ""
            (Right
                ( Predicated
                    { term = asPureMetaPattern (v1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
                    { term = asPureMetaPattern (v1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
            )
        )
    , testCase "Substituting a variable with a larger one."
        (assertEqualWithExplanation ""
            (Right
                ( Predicated
                    { term = asPureMetaPattern (y1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
                    { term = asPureMetaPattern (y1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
            )
        )
    , testCase "Substituting a variable with itself."
        (assertEqualWithExplanation ""
            (Right
                ( Predicated
                    { term = asPureMetaPattern (v1 PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(a, f(b))
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Merging configuration patterns."
        (assertEqualWithExplanation ""
            (Right
                ( Predicated
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
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) => x   vs   sigma(f(a), f(b))
    -- Expected: f(b) and a=b
    , testCase "Substitution with symbol matching."
        (assertEqualWithExplanation ""
            (Right
                ( Predicated
                    { term = asPureMetaPattern (metaF (b1 PatternSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( asVariable (a1 PatternSort)
                            , asPureMetaPattern (b1 PatternSort)
                            )
                        ]
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
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
                ( Predicated
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
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- x => exists a . x    vs    a
    -- Expected: exists <newvar> . a
    , testCase "Rename quantified rhs variables."
        (assertEqualWithExplanation ""
            (Right
                ( Predicated
                    { term =
                        asPureMetaPattern
                            (metaExists
                                PatternSort
                                (var_a1_0 PatternSort)
                                (a1 PatternSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings
                            [ variableRenaming
                                (a1 PatternSort) (var_a1_0 PatternSort)
                            ]
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) -> x   vs   sigma(g(a), f(b))
    -- Expected: error because g(a) != f(b)
    , testCase "Symbol clashes."
        (assertEqualWithExplanation ""
            (Right ExpandedPattern.bottom)
            (fst <$> runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(sigma(x, x), sigma(y, y)) -> sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), sigma(a, b))
    , testCase "Impossible substitution."
        (assertEqualWithExplanation ""
            (Right ExpandedPattern.bottom)
            (fst <$> runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "Impossible substitution (ctor)."
        (assertEqualWithExplanation ""
            (Right ExpandedPattern.bottom)
            (fst <$> runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "Substitution (non-ctor)."
        (assertEqualWithExplanation ""
            -- TODO(virgil): This should probably be a normal result with
            -- b=h(b) in the predicate.
            (Left
                (StepErrorSubstitution
                    (NonCtorCircularVariableDependency
                        [(asMetaVariable (b1 PatternSort))]
                    )
                )
            )
            (fst <$> runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "Substitution error (non-function)"
        (assertEqualWithExplanation ""
            (Left $ StepErrorUnification UnsupportedPatterns)
            (fst <$> runStep
                mockMetadataTools
                Predicated
                    { term =
                        asPureMetaPattern
                            (metaSigma
                                (a1 PatternSort)
                                (metaI (b1 PatternSort))
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
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
                    , axiomPatternAttributes = def
                    }
            )
        )
    -- sigma(x, x) -> x
    -- vs
    -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    , testCase "Unification is applied repeatedly"
        (assertEqualWithExplanation ""
            (Right Predicated
                { term = asPureMetaPattern
                    (metaSigma
                        (metaSigma (c1 PatternSort) (c1 PatternSort))
                        (metaSigma (c1 PatternSort) (c1 PatternSort))
                    )
                , predicate = makeTruePredicate
                , substitution =
                    [   ( asMetaVariable (a1 PatternSort)
                        , asPureMetaPattern
                            (metaSigma (c1 PatternSort) (c1 PatternSort))
                        )
                    ,   ( asMetaVariable (b1 PatternSort)
                        , asPureMetaPattern (c1 PatternSort)
                        )
                    ]
                }
            )
            (fst <$> runStep
                mockMetadataTools
                Predicated
                    { term = asPureMetaPattern
                        ( metaSigma
                            ( metaSigma (a1 PatternSort) (a1 PatternSort))
                            ( metaSigma
                                (metaSigma (b1 PatternSort) (c1 PatternSort))
                                (metaSigma (b1 PatternSort) (b1 PatternSort))
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = []
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
                    , axiomPatternAttributes = def
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
                    ( Predicated
                        { term = asPureMetaPattern (metaSigma fOfB fOfB)
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( asVariable (a1 PatternSort)
                                , asPureMetaPattern fOfB
                                )
                            ]
                        }
                    , mconcat
                        (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                )
                (runStep
                    mockMetadataTools
                    Predicated
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
                        , axiomPatternAttributes = def
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
                    ( Predicated
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
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                )
                (runStep
                    mockMetadataTools
                    Predicated
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
                        , axiomPatternAttributes = def
                        }
                )
            )
    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "Matching different string literals is bottom"
        (assertEqualWithExplanation ""
            (Right ExpandedPattern.bottom)
            (fst <$> runStep
                mockMetadataTools
                Predicated
                    { term = asPurePattern
                        ( StringLiteralPattern (StringLiteral "sl2")
                        :: UnFixedPureMLPattern Meta Variable
                        )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = asPurePattern
                        ( StringLiteralPattern (StringLiteral "sl1")
                        :: UnFixedPureMLPattern Meta Variable
                        )
                    , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
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
                ( Predicated
                    { term = asPureMetaPattern (a1 PatternSort)
                    , predicate =
                        makeEquals
                            (metaG (a1 PatternSort))
                            (metaF (a1 PatternSort))
                    , substitution = []
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
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
        testCase "Substitution_normalization."
            (assertEqualWithExplanation ""
                (Right
                    ( Predicated
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
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                )
                (runStep
                    mockMetadataTools
                    Predicated
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
                        , axiomPatternAttributes = def
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
                  ( Predicated
                      { term = asPureMetaPattern (a1 PatternSort)
                      , predicate = preCondition a1
                      , substitution = []
                      }
                  , mconcat
                      (map stepProof
                          [ StepProofVariableRenamings []
                          , StepProofUnification EmptyUnificationProof
                          ]
                      )
                  )
              )
              (runStep
                  mockMetadataTools
                  Predicated
                      { term = asPureMetaPattern (a1 PatternSort)
                      , predicate = makeTruePredicate
                      , substitution = []
                      }
                  AxiomPattern
                      { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
                      , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
                      , axiomPatternRequires = preCondition x1
                      , axiomPatternAttributes = def
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
    var_a1_0 :: MetaSort sort => sort -> MetaVariable sort
    var_a1_0 = metaVariable "#var_a1_0" AstLocationTest
    variableRenaming
        :: MetaSort sort
        => MetaVariable sort
        -> MetaVariable sort
        -> VariableRenaming Meta Variable
    variableRenaming from to =
        VariableRenaming
            { variableRenamingOriginal = AxiomVariable (asMetaVariable from)
            , variableRenamingRenamed =
                ConfigurationVariable (asMetaVariable to)
            }
    identicalVariablesAssertion var =
        assertEqualWithExplanation ""
            (Right
                ( Predicated
                    { term =
                        asPureMetaPattern (var PatternSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
            )
            (runStep
                mockMetadataTools
                Predicated
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
                    , axiomPatternAttributes = def
                    }
            )

mockStepperAttributes :: SymbolOrAlias Meta -> StepperAttributes
mockStepperAttributes patternHead =
    defaultStepperAttributes
        { constructor = Constructor { isConstructor }
        , functional = Functional { isDeclaredFunctional }
        , function = Function { isDeclaredFunction }
        , injective = Injective { isDeclaredInjective }
        }
  where
    isConstructor = patternHead /= hSymbol && patternHead /= iSymbol
    isDeclaredFunctional = patternHead /= iSymbol
    isDeclaredFunction = patternHead /= iSymbol
    isDeclaredInjective = patternHead /= hSymbol && patternHead /= iSymbol

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = mockStepperAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = undefined
    , symbolOrAliasSorts = mockSymbolOrAliasSorts
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
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
    give (symbolOrAliasSorts mockMetadataTools)
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

iSymbol :: SymbolOrAlias Meta
iSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#i" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaI p1 = MetaI p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaI p1)
  where
    asProperPattern (MetaI p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = iSymbol
            , applicationChildren = [asAst p1]
            }
metaI
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaI p1
metaI = MetaI

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> AxiomPattern level
    -> Either
        (StepError level Variable)
        (CommonExpandedPattern level, StepProof level Variable)
runStep metadataTools configuration axiom =
    SMT.unsafeRunSMT SMT.defaultConfig
    $ evalSimplifier
    $ runExceptT
    $ stepWithAxiom
        metadataTools
        (Mock.substitutionSimplifier metadataTools)
        configuration
        axiom
