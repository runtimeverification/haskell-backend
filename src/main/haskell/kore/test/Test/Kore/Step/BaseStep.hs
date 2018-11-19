module Test.Kore.Step.BaseStep (test_baseStep) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Control.Monad.Except
                 ( runExceptT )
import qualified Data.Bifunctor as Bifunctor
import           Data.Default
                 ( def )
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate
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

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Tasty.HUnit.Extensions

test_baseStep :: [TestTree]
test_baseStep =
    give mockSymbolOrAliasSorts
    [ testCase "Substituting a variable." $ do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ v1 patternMetaSort
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
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term = Var_ $ v1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "Substituting a variable with a larger one." $ do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ y1 patternMetaSort
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
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term = Var_ $ y1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "Substituting a variable with itself." $ do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ v1 patternMetaSort
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
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (Var_ $ v1 patternMetaSort)
                            (Var_ $ v1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) => x   vs   sigma(a, f(b))
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Merging configuration patterns." $ do
        let expect =
                Right
                    ( Predicated
                        { term = metaF (Var_ $ b1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution =
                            [   ( a1 patternMetaSort
                                , metaF (Var_ $ b1 patternMetaSort)
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
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (Var_ $ a1 patternMetaSort)
                            (metaF (Var_ $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) => x   vs   sigma(f(a), f(b))
    -- Expected: f(b) and a=b
    , testCase "Substitution with symbol matching." $ do
        let expect =
                Right
                    ( Predicated
                        { term = metaF (Var_ $ b1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution =
                            [(a1 patternMetaSort, Var_ $ b1 patternMetaSort)]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaF $ Var_ $ a1 patternMetaSort)
                            (metaF $ Var_ $ b1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

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
    , testCase "Merge multiple variables." $ do
        let expect =
                Right
                    ( Predicated
                        { term =
                            metaSigma
                                (Var_ $ b1 patternMetaSort)
                                (Var_ $ b1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution =
                            [(a1 patternMetaSort, Var_ $ b1 patternMetaSort)]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (Var_ $ a1 patternMetaSort)
                                (Var_ $ b1 patternMetaSort)
                            )
                            (metaSigma
                                (Var_ $ b1 patternMetaSort)
                                (Var_ $ a1 patternMetaSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (metaSigma
                                (Var_ $ y1 patternMetaSort)
                                (Var_ $ y1 patternMetaSort)
                            )
                    , axiomPatternRight =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect actual

    -- x => exists a . x    vs    a
    -- Expected: exists <newvar> . a
    , testCase "Rename quantified rhs variables." $ do
        let expect =
                Right
                    ( Predicated
                        { term =
                            Exists_
                                patternMetaSort
                                (var_a1_0 patternMetaSort)
                                (Var_ $ a1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings
                                [ variableRenaming
                                    (a1 patternMetaSort)
                                    (var_a1_0 patternMetaSort)
                                ]
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term = Var_ $ a1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = Var_ $ x1 patternMetaSort
                    , axiomPatternRight =
                        Exists_
                            patternMetaSort
                            (a1 patternMetaSort)
                            (Var_ $ x1 patternMetaSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x   vs   sigma(g(a), f(b))
    -- Expected: error because g(a) != f(b)
    , testCase "Symbol clashes." $ do
        let expect = Right ExpandedPattern.bottom
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaG (Var_ $ a1 patternMetaSort))
                            (metaF (Var_ $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect (Bifunctor.second fst actual)

    -- sigma(sigma(x, x), sigma(y, y)) -> sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), sigma(a, b))
    , testCase "Impossible substitution." $ do
        let expect = Right ExpandedPattern.bottom
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (Var_ $ a1 patternMetaSort)
                                (metaF (Var_ $ b1 patternMetaSort))
                            )
                            (metaSigma
                                (Var_ $ a1 patternMetaSort)
                                (Var_ $ b1 patternMetaSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (metaSigma
                                (Var_ $ y1 patternMetaSort)
                                (Var_ $ y1 patternMetaSort)
                            )
                    , axiomPatternRight =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect (Bifunctor.second fst actual)

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "Impossible substitution (ctor)." $ do
        let expect = Right ExpandedPattern.bottom
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (Var_ $ a1 patternMetaSort)
                            (metaF (Var_ $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [(b1 patternMetaSort, Var_ $ a1 patternMetaSort)]
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect (Bifunctor.second fst actual)

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "Substitution (non-ctor)." $ do
        let expect =
                -- TODO(virgil): This should probably be a normal result with
                -- b=h(b) in the predicate.
                Left
                    (StepErrorSubstitution
                        (NonCtorCircularVariableDependency
                            [b1 patternMetaSort]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (Var_ $ a1 patternMetaSort)
                            (metaH (Var_ $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [(b1 patternMetaSort, Var_ $ a1 patternMetaSort)]
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "Substitution error (non-function)" $ do
        let expect = Left $ StepErrorUnification UnsupportedPatterns
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (Var_ $ a1 patternMetaSort)
                            (metaI (Var_ $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    , testCase "Unification is applied repeatedly" $ do
        let expect =
                Right Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (Var_ $ c1 patternMetaSort)
                                (Var_ $ c1 patternMetaSort)
                            )
                            (metaSigma
                                (Var_ $ c1 patternMetaSort)
                                (Var_ $ c1 patternMetaSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( a1 patternMetaSort
                            , metaSigma
                                (Var_ $ c1 patternMetaSort)
                                (Var_ $ c1 patternMetaSort)
                            )
                        ,   ( b1 patternMetaSort
                            , Var_ $ c1 patternMetaSort
                            )
                        ]
                    }
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (Var_ $ a1 patternMetaSort)
                                (Var_ $ a1 patternMetaSort)
                            )
                            (metaSigma
                                (metaSigma
                                    (Var_ $ b1 patternMetaSort)
                                    (Var_ $ c1 patternMetaSort)
                                )
                                (metaSigma
                                    (Var_ $ b1 patternMetaSort)
                                    (Var_ $ b1 patternMetaSort)
                                )
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect (Bifunctor.second fst actual)

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Substitution normalization." $ do
        let
            fOfB = metaF (Var_ $ b1 patternMetaSort)
            expect =
                Right
                    ( Predicated
                        { term = metaSigma fOfB fOfB
                        , predicate = makeTruePredicate
                        , substitution =
                            [(a1 patternMetaSort, fOfB)]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (Var_ $ a1 patternMetaSort)
                                fOfB
                            )
                            (Var_ $ a1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        (metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (Var_ $ y1 patternMetaSort)
                        )
                    , axiomPatternRight =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    , testCase "Merging substitution with existing one." $ do
        let
            fOfB = metaF (Var_ $ b1 patternMetaSort)
            fOfC = metaF (Var_ $ c1 patternMetaSort)
            expect =
                Right
                    ( Predicated
                        { term = metaSigma fOfC fOfC
                        , predicate = makeTruePredicate
                        , substitution =
                            [ (a1 patternMetaSort, fOfC)
                            , (b1 patternMetaSort, Var_ $ c1 patternMetaSort)
                            ]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma (Var_ $ a1 patternMetaSort) fOfB)
                            (Var_ $ a1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution =
                        [(a1 patternMetaSort, fOfC)]
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRight =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect actual

    -- "sl1" => x
    -- vs
    -- "sl2"
    -- Expected: bottom
    , testCase "Matching different string literals is bottom" $ do
        let expect = Right ExpandedPattern.bottom
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term = StringLiteral_ "sl2"
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft = StringLiteral_ "sl1"
                    , axiomPatternRight = Var_ $ x1 patternMetaSort
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect (Bifunctor.second fst actual)

    -- x => x
    -- vs
    -- a and g(a)=f(a)
    -- Expected: y1 and g(a)=f(a)
    , testCase "Preserving initial condition." $ do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ a1 patternMetaSort
                        , predicate =
                            makeEqualsPredicate
                                (metaG (Var_ $ a1 patternMetaSort))
                                (metaF (Var_ $ a1 patternMetaSort))
                        , substitution = []
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term = Var_ $ a1 patternMetaSort
                    , predicate =
                        makeEqualsPredicate
                            (metaG (Var_ $ a1 patternMetaSort))
                            (metaF (Var_ $ a1 patternMetaSort))
                    , substitution = []
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a) and g(a)=f(a)
    -- Expected: sigma(f(b), f(b)) and a=f(b) and and g(f(b))=f(f(b))
    , testCase "Substitution_normalization." $ do
        let
            fOfB = metaF (Var_ $ b1 patternMetaSort)
            expect =
                Right
                    ( Predicated
                        { term = metaSigma fOfB fOfB
                        , predicate =
                            makeEqualsPredicate (metaG fOfB) (metaF fOfB)
                        , substitution =
                            [(a1 patternMetaSort, fOfB)]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (Var_ $ a1 patternMetaSort)
                                fOfB
                            )
                            (Var_ $ a1 patternMetaSort)
                    , predicate =
                        makeEqualsPredicate
                            (metaG (Var_ $ a1 patternMetaSort))
                            (metaF (Var_ $ a1 patternMetaSort))
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRight =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect actual

    -- x => x requires g(x)=f(x)
    -- vs
    -- a
    -- Expected: y1 and g(a)=f(a)
    , testCase "Conjoins axiom pre-condition" $ do
        let
            preCondition var =
                makeEqualsPredicate
                    (metaG (Var_ $ var patternMetaSort))
                    (metaF (Var_ $ var patternMetaSort))
            expect =
              Right
                  ( Predicated
                      { term = Var_ $ a1 patternMetaSort
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
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term = Var_ $ a1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                axiomId { axiomPatternRequires = preCondition x1 }
        assertEqualWithExplanation "" expect actual

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
    v1, a1, b1, c1, x1, y1, var_a1_0 :: Sort Meta -> Variable Meta
    v1 = Variable (testId "#v1")
    a1 = Variable (testId "#a1")
    b1 = Variable (testId "#b1")
    c1 = Variable (testId "#c1")
    x1 = Variable (testId "#x1")
    y1 = Variable (testId "#y1")
    var_a1_0 = Variable (testId "#var_a1_0")
    variableRenaming
        :: Variable Meta
        -> Variable Meta
        -> VariableRenaming Meta Variable
    variableRenaming from to =
        VariableRenaming
            { variableRenamingOriginal = AxiomVariable from
            , variableRenamingRenamed = ConfigurationVariable to
            }

    identicalVariablesAssertion var = do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ var patternMetaSort
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
        actual <-
            runStep
                mockMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (Var_ $ var patternMetaSort)
                            (Var_ $ var patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                AxiomPattern
                    { axiomPatternLeft =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ x1 patternMetaSort)
                    , axiomPatternRight = Var_ $ x1 patternMetaSort
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
        assertEqualWithExplanation "" expect actual

    axiomId =
        AxiomPattern
            { axiomPatternLeft = Var_ $ x1 patternMetaSort
            , axiomPatternRight = Var_ $ x1 patternMetaSort
            , axiomPatternRequires = makeTruePredicate
            , axiomPatternAttributes = def
            }

    axiomMetaSigmaId =
        AxiomPattern
            { axiomPatternLeft =
                metaSigma
                    (Var_ $ x1 patternMetaSort)
                    (Var_ $ x1 patternMetaSort)
            , axiomPatternRight =
                Var_ $ x1 patternMetaSort
            , axiomPatternRequires = makeTruePredicate
            , axiomPatternAttributes = def
            }

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
    { applicationSortsOperands = [patternMetaSort, patternMetaSort]
    , applicationSortsResult = patternMetaSort
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

sigmaSymbol :: SymbolOrAlias Meta
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#sigma"
    , symbolOrAliasParams = []
    }

metaSigma
    :: CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
metaSigma p1 p2 = App_ sigmaSymbol [p1, p2]


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#f"
    , symbolOrAliasParams = []
    }

metaF :: CommonPurePattern Meta dom -> CommonPurePattern Meta dom
metaF p = App_ fSymbol [p]


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#g"
    , symbolOrAliasParams = []
    }

metaG :: CommonPurePattern Meta dom -> CommonPurePattern Meta dom
metaG p = App_ gSymbol [p]

hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#h"
    , symbolOrAliasParams = []
    }

metaH :: CommonPurePattern Meta dom -> CommonPurePattern Meta dom
metaH p = App_ hSymbol [p]

iSymbol :: SymbolOrAlias Meta
iSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#i" AstLocationTest
    , symbolOrAliasParams = []
    }

metaI :: CommonPurePattern Meta dom -> CommonPurePattern Meta dom
metaI p = App_ iSymbol [p]

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> AxiomPattern level
    -> IO
        (Either
            (StepError level Variable)
            (CommonExpandedPattern level, StepProof level Variable)
        )
runStep metadataTools configuration axiom =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ runExceptT
    $ stepWithAxiom
        metadataTools
        (Mock.substitutionSimplifier metadataTools)
        configuration
        axiom
