module Test.Kore.Step.BaseStep (test_baseStep, test_baseStepRemainder) where

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

import           Kore.AST.Pure
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkVar )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
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
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unifier
                 ( UnificationError (..), UnificationProof (..) )
import qualified SMT

import           Test.Kore
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
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
                        , substitution = mempty
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
                    , substitution = mempty
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "Substituting a variable with a larger one." $ do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ y1 patternMetaSort
                        , predicate = makeTruePredicate
                        , substitution = mempty
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
                    , substitution = mempty
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "Substituting a variable with itself." $ do
        let expect =
                Right
                    ( Predicated
                        { term = Var_ $ v1 patternMetaSort
                        , predicate = makeTruePredicate
                        , substitution = mempty
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
                    , substitution = mempty
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
                        , substitution = Substitution.wrap
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
                    , substitution = mempty
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
                        , substitution = Substitution.wrap
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
                    , substitution = mempty
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
                        , substitution = Substitution.wrap
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (metaSigma
                                (Var_ $ y1 patternMetaSort)
                                (Var_ $ y1 patternMetaSort)
                            )
                    , right =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                        , substitution = mempty
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left = Var_ $ x1 patternMetaSort
                    , right =
                        Exists_
                            patternMetaSort
                            (a1 patternMetaSort)
                            (Var_ $ x1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                    , substitution = mempty
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (metaSigma
                                (Var_ $ y1 patternMetaSort)
                                (Var_ $ y1 patternMetaSort)
                            )
                    , right =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                    , substitution = Substitution.wrap
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
                    , substitution = Substitution.wrap
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
                    , substitution = mempty
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
                    , substitution = Substitution.wrap
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
                    , substitution = mempty
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
                        , substitution = Substitution.wrap
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        (metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (Var_ $ y1 patternMetaSort)
                        )
                    , right =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                        , substitution = Substitution.wrap
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
                    , substitution = Substitution.wrap
                        [(a1 patternMetaSort, fOfC)]
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (Var_ $ y1 patternMetaSort)
                    , right =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left = StringLiteral_ "sl1"
                    , right = Var_ $ x1 patternMetaSort
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                        , substitution = mempty
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
                    , substitution = mempty
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
                        , substitution = Substitution.wrap
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (Var_ $ x1 patternMetaSort)
                                (Var_ $ x1 patternMetaSort)
                            )
                            (Var_ $ y1 patternMetaSort)
                    , right =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
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
                      , substitution = mempty
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
                    , substitution = mempty
                    }
                (RewriteRule ruleId { requires = preCondition x1 })
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
                        , substitution = mempty
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
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (Var_ $ x1 patternMetaSort)
                            (Var_ $ x1 patternMetaSort)
                    , right = Var_ $ x1 patternMetaSort
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
        assertEqualWithExplanation "" expect actual

    ruleId =
        RulePattern
            { left = Var_ $ x1 patternMetaSort
            , right = Var_ $ x1 patternMetaSort
            , requires = makeTruePredicate
            , attributes = def
            }
    axiomId = RewriteRule ruleId

    axiomMetaSigmaId =
        RewriteRule RulePattern
            { left =
                metaSigma
                    (Var_ $ x1 patternMetaSort)
                    (Var_ $ x1 patternMetaSort)
            , right =
                Var_ $ x1 patternMetaSort
            , requires = makeTruePredicate
            , attributes = def
            }

test_baseStepRemainder :: [TestTree]
test_baseStepRemainder = give mockSymbolOrAliasSortsR
    [ testCase "If-then" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: if x then cg
        --   axiom: if true y => y
        -- Actual:
        --   term: constr20(x, cg)
        --   axiom: constr20(a, y) => y
        -- Expected:
        --   rewritten: cg, with ⌈cg⌉ and [x=a]
        --   remainder: constr20(x, cg), with ¬(⌈cg⌉ and x=a)
        let
            expected = Right
                ( StepResult
                    { rewrittenPattern = Predicated
                        { term = Mock.cg
                        , predicate = makeCeilPredicate Mock.cg
                        , substitution =
                            Substitution.wrap [(Mock.x, Mock.a)]
                        }
                    , remainder = Predicated
                        { term = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                        , predicate =
                            makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                                )
                        , substitution = mempty
                        }
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
        actual <- runStepWithRemainder
            mockMetadataToolsR
            Predicated
                { term = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (RewriteRule RulePattern
                { left =
                    Mock.functionalConstr20 Mock.a (mkVar Mock.y)
                , right = mkVar Mock.y
                , requires = makeTruePredicate
                , attributes = def
                }
            )
        assertEqualWithExplanation "" expected actual
    , testCase "If-then with existing predicate" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: if x then cg
        --   axiom: if true y => y
        -- Actual:
        --   term: constr20(x, cg), with a ⌈cf⌉ predicate
        --   axiom: constr20(a, y) => y
        -- Expected:
        --   rewritten: cg, with ⌈cf⌉ and ⌈cg⌉ and [x=a]
        --   remainder: constr20(x, cg), with ⌈cf⌉ and ¬(⌈cg⌉ and x=a)
        let
            expected = Right
                ( StepResult
                    { rewrittenPattern = Predicated
                        { term = Mock.cg
                        , predicate = makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeCeilPredicate Mock.cg)
                        , substitution = Substitution.wrap
                            [(Mock.x, Mock.a)]
                        }
                    , remainder = Predicated
                        { term = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                        , predicate = makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeNotPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate Mock.cg)
                                    (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                                )
                            )
                        , substitution = mempty
                        }
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
        actual <- runStepWithRemainder
            mockMetadataToolsR
            Predicated
                { term = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                , predicate = makeCeilPredicate Mock.cf
                , substitution = mempty
                }
            (RewriteRule RulePattern
                { left =
                    Mock.functionalConstr20 Mock.a (mkVar Mock.y)
                , right = mkVar Mock.y
                , requires = makeTruePredicate
                , attributes = def
                }
            )
        assertEqualWithExplanation "" expected actual
    , testCase "signum - side condition" $ do
        -- This uses `functionalConstr20(x, y)` instead of `if x then y`
        -- and `a` instead of `true`.
        --
        -- Intended:
        --   term: signum(x)
        --   axiom: signum(y) => -1 if (y<0 == true)
        -- Actual:
        --   term: functionalConstr10(x)
        --   axiom: functionalConstr10(y) => a if f(y) == b
        -- Expected:
        --   rewritten: a, with f(x) == b
        --   remainder: functionalConstr10(x), with ¬(f(x) == b)
        let
            expected = Right
                ( StepResult
                    { rewrittenPattern = Predicated
                        { term = Mock.a
                        , predicate =
                            makeEqualsPredicate (Mock.f (mkVar Mock.x)) Mock.b
                        , substitution = mempty
                        }
                    , remainder = Predicated
                        { term = Mock.functionalConstr10 (mkVar Mock.x)
                        , predicate =
                            makeNotPredicate
                                (makeEqualsPredicate
                                    (Mock.f (mkVar Mock.x))
                                    Mock.b
                                )
                        , substitution = mempty
                        }
                    }
                , mconcat
                    (map stepProof
                        [ StepProofVariableRenamings []
                        , StepProofUnification EmptyUnificationProof
                        ]
                    )
                )
        actual <- runStepWithRemainder
            mockMetadataToolsR
            Predicated
                { term = Mock.functionalConstr10 (mkVar Mock.x)
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (RewriteRule RulePattern
                { left =
                    Mock.functionalConstr10 (mkVar Mock.y)
                , right = Mock.a
                , requires =
                    makeEqualsPredicate (Mock.f (mkVar Mock.y)) Mock.b
                , attributes = def
                }
            )
        assertEqualWithExplanation "" expected actual
    ]
  where
    mockSymbolOrAliasSortsR :: SymbolOrAliasSorts Object
    mockSymbolOrAliasSortsR =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    mockMetadataToolsR :: MetadataTools Object StepperAttributes
    mockMetadataToolsR =
        Mock.makeMetadataTools
            mockSymbolOrAliasSortsR
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.sortAttributesMapping
            Mock.subsorts

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
    :: Functor domain
    => CommonPurePattern Meta domain
    -> CommonPurePattern Meta domain
    -> CommonPurePattern Meta domain
metaSigma p1 p2 = App_ sigmaSymbol [p1, p2]


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#f"
    , symbolOrAliasParams = []
    }

metaF
    :: Functor domain
    => CommonPurePattern Meta domain
    -> CommonPurePattern Meta domain
metaF p = App_ fSymbol [p]


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#g"
    , symbolOrAliasParams = []
    }

metaG
    :: Functor domain
    => CommonPurePattern Meta domain
    -> CommonPurePattern Meta domain
metaG p = App_ gSymbol [p]

hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#h"
    , symbolOrAliasParams = []
    }

metaH
    :: Functor domain
    => CommonPurePattern Meta domain
    -> CommonPurePattern Meta domain
metaH p = App_ hSymbol [p]

iSymbol :: SymbolOrAlias Meta
iSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#i" AstLocationTest
    , symbolOrAliasParams = []
    }

metaI
    :: Functor domain
    => CommonPurePattern Meta domain
    -> CommonPurePattern Meta domain
metaI p = App_ iSymbol [p]

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> RewriteRule level
    -> IO
        (Either
            (StepError level Variable)
            (CommonExpandedPattern level, StepProof level Variable)
        )
runStep metadataTools configuration axiom = do
    ioResult <-
        runStepWithRemainder metadataTools configuration axiom
    return $ do
        (StepResult { rewrittenPattern }, proof) <- ioResult
        return (rewrittenPattern, proof)

runStepWithRemainder
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> RewriteRule level
    -> IO
        (Either
            (StepError level Variable)
            (StepResult level Variable, StepProof level Variable)
        )
runStepWithRemainder metadataTools configuration axiom =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ runExceptT
    $ stepWithRule
        metadataTools
        (Mock.substitutionSimplifier metadataTools)
        configuration
        axiom
