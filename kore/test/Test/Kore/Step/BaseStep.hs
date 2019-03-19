{-# LANGUAGE OverloadedLists #-}

module Test.Kore.Step.BaseStep
    ( test_baseStep
    , test_baseStepRemainder
    , test_baseStepMultipleRemainder
    , test_instantiateRule
    , test_applyRule
    , test_unifyRule
    , test_stepWithRewriteRuleBranch
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Monad.Except
                 ( ExceptT, runExceptT )
import           Data.Default as Default
                 ( def )
import qualified Data.Either as Either
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Data.Sup
import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (..) )
import qualified Kore.Step.AxiomPatterns as RulePattern
import           Kore.Step.BaseStep hiding
                 ( applyRule, instantiateRule, stepWithRewriteRuleBranch,
                 unifyRule )
import qualified Kore.Step.BaseStep as BaseStep
import           Kore.Step.Error
import           Kore.Step.Pattern as Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern,
                 PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unifier
                 ( UnificationError (..), UnificationProof (..) )
import           Kore.Variables.Fresh
                 ( nextVariable )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_baseStep :: [TestTree]
test_baseStep =
    [ testCase "Substituting a variable." $ do
        let expect = Right
                [   ( Predicated
                        { term = mkVar $ v1 patternMetaSort
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term = mkVar $ v1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "Substituting a variable with a larger one." $ do
        let expect = Right
                [   ( Predicated
                        { term = mkVar $ y1 patternMetaSort
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term = mkVar $ y1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "Substituting a variable with itself." $ do
        let expect = Right
                [   ( Predicated
                        { term = mkVar $ v1 patternMetaSort
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (mkVar $ v1 patternMetaSort)
                            (mkVar $ v1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) => x   vs   sigma(a, f(b))
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Merging configuration patterns." $ do
        let expect = Right
                [   ( Predicated
                        { term = metaF (mkVar $ b1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [   ( a1 patternMetaSort
                                , metaF (mkVar $ b1 patternMetaSort)
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (mkVar $ a1 patternMetaSort)
                            (metaF (mkVar $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) => x   vs   sigma(f(a), f(b))
    -- Expected: f(b) and a=b
    , testCase "Substitution with symbol matching." $ do
        let expect = Right
                [   ( Predicated
                        { term = metaF (mkVar $ b1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [(a1 patternMetaSort, mkVar $ b1 patternMetaSort)]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaF $ mkVar $ a1 patternMetaSort)
                            (metaF $ mkVar $ b1 patternMetaSort)
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
        let expect = Right
                [   ( Predicated
                        { term =
                            metaSigma
                                (mkVar $ b1 patternMetaSort)
                                (mkVar $ b1 patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [(a1 patternMetaSort, mkVar $ b1 patternMetaSort)]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (mkVar $ a1 patternMetaSort)
                                (mkVar $ b1 patternMetaSort)
                            )
                            (metaSigma
                                (mkVar $ b1 patternMetaSort)
                                (mkVar $ a1 patternMetaSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (mkVar $ x1 patternMetaSort)
                                (mkVar $ x1 patternMetaSort)
                            )
                            (metaSigma
                                (mkVar $ y1 patternMetaSort)
                                (mkVar $ y1 patternMetaSort)
                            )
                    , right =
                        metaSigma
                            (mkVar $ x1 patternMetaSort)
                            (mkVar $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
        assertEqualWithExplanation "" expect actual

    -- x => exists a . x    vs    a
    -- Expected: exists <newvar> . a
    , testCase "Rename quantified rhs variables." $ do
        let expect = Right
                [   ( Predicated
                        { term =
                            mkExists
                                (var_a1_0 patternMetaSort)
                                (mkVar $ a1 patternMetaSort)
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term = mkVar $ a1 patternMetaSort
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left = mkVar $ x1 patternMetaSort
                    , right =
                        mkExists
                            (a1 patternMetaSort)
                            (mkVar $ x1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x   vs   sigma(g(a), f(b))
    -- Expected: error because g(a) != f(b)
    , testCase "Symbol clashes." $ do
        let expect = Right []
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaG (mkVar $ a1 patternMetaSort))
                            (metaF (mkVar $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect (fmap (map fst) actual)

    -- sigma(sigma(x, x), sigma(y, y)) -> sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), sigma(a, b))
    , testCase "Impossible substitution." $ do
        let expect = Right []
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (mkVar $ a1 patternMetaSort)
                                (metaF (mkVar $ b1 patternMetaSort))
                            )
                            (metaSigma
                                (mkVar $ a1 patternMetaSort)
                                (mkVar $ b1 patternMetaSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (mkVar $ x1 patternMetaSort)
                                (mkVar $ x1 patternMetaSort)
                            )
                            (metaSigma
                                (mkVar $ y1 patternMetaSort)
                                (mkVar $ y1 patternMetaSort)
                            )
                    , right =
                        metaSigma
                            (mkVar $ x1 patternMetaSort)
                            (mkVar $ y1 patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
        assertEqualWithExplanation "" expect (fmap (map fst) actual)

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "Impossible substitution (ctor)." $ do
        let expect = Right [ExpandedPattern.bottom]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (mkVar $ a1 patternMetaSort)
                            (metaF (mkVar $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap
                        [(b1 patternMetaSort, mkVar $ a1 patternMetaSort)]
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect (fmap (map fst) actual)

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
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (mkVar $ a1 patternMetaSort)
                            (metaH (mkVar $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap
                        [(b1 patternMetaSort, mkVar $ a1 patternMetaSort)]
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
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (mkVar $ a1 patternMetaSort)
                            (metaI (mkVar $ b1 patternMetaSort))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    , testCase "Unification is applied repeatedly" $ do
        let expect = Right
                [ Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (mkVar $ c1 patternMetaSort)
                                (mkVar $ c1 patternMetaSort)
                            )
                            (metaSigma
                                (mkVar $ c1 patternMetaSort)
                                (mkVar $ c1 patternMetaSort)
                            )
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap
                        [   ( a1 patternMetaSort
                            , metaSigma
                                (mkVar $ c1 patternMetaSort)
                                (mkVar $ c1 patternMetaSort)
                            )
                        ,   ( b1 patternMetaSort
                            , mkVar $ c1 patternMetaSort
                            )
                        ]
                    }
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (mkVar $ a1 patternMetaSort)
                                (mkVar $ a1 patternMetaSort)
                            )
                            (metaSigma
                                (metaSigma
                                    (mkVar $ b1 patternMetaSort)
                                    (mkVar $ c1 patternMetaSort)
                                )
                                (metaSigma
                                    (mkVar $ b1 patternMetaSort)
                                    (mkVar $ b1 patternMetaSort)
                                )
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                axiomMetaSigmaId
        assertEqualWithExplanation "" expect (fmap (map fst) actual)

    -- sigma(sigma(x, x), y) => sigma(x, y)
    -- vs
    -- sigma(sigma(a, f(b)), a)
    -- Expected: sigma(f(b), f(b)) and a=f(b)
    , testCase "Substitution normalization." $ do
        let
            fOfB = metaF (mkVar $ b1 patternMetaSort)
            expect = Right
                [   ( Predicated
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (mkVar $ a1 patternMetaSort)
                                fOfB
                            )
                            (mkVar $ a1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (mkVar $ x1 patternMetaSort)
                                (mkVar $ x1 patternMetaSort)
                            )
                            (mkVar $ y1 patternMetaSort)
                    , right =
                        metaSigma
                            (mkVar $ x1 patternMetaSort)
                            (mkVar $ y1 patternMetaSort)
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
            fOfB = metaF (mkVar $ b1 patternMetaSort)
            fOfC = metaF (mkVar $ c1 patternMetaSort)
            expect = Right
                [   ( Predicated
                        { term = metaSigma fOfC fOfC
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (a1 patternMetaSort, fOfC)
                            , (b1 patternMetaSort, mkVar $ c1 patternMetaSort)
                            ]
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma (mkVar $ a1 patternMetaSort) fOfB)
                            (mkVar $ a1 patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap
                        [(a1 patternMetaSort, fOfC)]
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (mkVar $ x1 patternMetaSort)
                                (mkVar $ x1 patternMetaSort)
                            )
                            (mkVar $ y1 patternMetaSort)
                    , right =
                        metaSigma
                            (mkVar $ x1 patternMetaSort)
                            (mkVar $ y1 patternMetaSort)
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
        let expect = Right []
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term = mkStringLiteral "sl2"
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left = mkStringLiteral "sl1"
                    , right = mkVar $ x1 patternMetaSort
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
        assertEqualWithExplanation "" expect (fmap (map fst) actual)

    -- x => x
    -- vs
    -- a and g(a)=f(a)
    -- Expected: y1 and g(a)=f(a)
    , testCase "Preserving initial condition." $ do
        let expect = Right
                [   ( Predicated
                        { term = mkVar $ a1 patternMetaSort
                        , predicate =
                            makeEqualsPredicate
                                (metaG (mkVar $ a1 patternMetaSort))
                                (metaF (mkVar $ a1 patternMetaSort))
                        , substitution = mempty
                        }
                    , mconcat
                        (map stepProof
                            [ StepProofVariableRenamings []
                            , StepProofUnification EmptyUnificationProof
                            ]
                        )
                    )
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term = mkVar $ a1 patternMetaSort
                    , predicate =
                        makeEqualsPredicate
                            (metaG (mkVar $ a1 patternMetaSort))
                            (metaF (mkVar $ a1 patternMetaSort))
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
            fOfB = metaF (mkVar $ b1 patternMetaSort)
            expect = Right
                [   ( Predicated
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (metaSigma
                                (mkVar $ a1 patternMetaSort)
                                fOfB
                            )
                            (mkVar $ a1 patternMetaSort)
                    , predicate =
                        makeEqualsPredicate
                            (metaG (mkVar $ a1 patternMetaSort))
                            (metaF (mkVar $ a1 patternMetaSort))
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (metaSigma
                                (mkVar $ x1 patternMetaSort)
                                (mkVar $ x1 patternMetaSort)
                            )
                            (mkVar $ y1 patternMetaSort)
                    , right =
                        metaSigma
                            (mkVar $ x1 patternMetaSort)
                            (mkVar $ y1 patternMetaSort)
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
                    (metaG (mkVar $ var patternMetaSort))
                    (metaF (mkVar $ var patternMetaSort))
            expect = Right
                [   ( Predicated
                        { term = mkVar $ a1 patternMetaSort
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term = mkVar $ a1 patternMetaSort
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
    v1 = Variable (testId "#v1") mempty
    a1 = Variable (testId "#a1") mempty
    b1 = Variable (testId "#b1") mempty
    c1 = Variable (testId "#c1") mempty
    x1 = Variable (testId "#x1") mempty
    y1 = Variable (testId "#y1") mempty
    var_a1_0 = Variable (testId "#a1") (Just (Element 0))

    identicalVariablesAssertion var = do
        let expect = Right
                [   ( Predicated
                        { term = mkVar $ var patternMetaSort
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
                ]
        actual <-
            runStep
                mockMetaMetadataTools
                Predicated
                    { term =
                        metaSigma
                            (mkVar $ var patternMetaSort)
                            (mkVar $ var patternMetaSort)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (RewriteRule RulePattern
                    { left =
                        metaSigma
                            (mkVar $ x1 patternMetaSort)
                            (mkVar $ x1 patternMetaSort)
                    , right = mkVar $ x1 patternMetaSort
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
        assertEqualWithExplanation "" expect actual

    ruleId =
        RulePattern
            { left = mkVar $ x1 patternMetaSort
            , right = mkVar $ x1 patternMetaSort
            , requires = makeTruePredicate
            , attributes = def
            }
    axiomId = RewriteRule ruleId

    axiomMetaSigmaId =
        RewriteRule RulePattern
            { left =
                metaSigma
                    (mkVar $ x1 patternMetaSort)
                    (mkVar $ x1 patternMetaSort)
            , right =
                mkVar $ x1 patternMetaSort
            , requires = makeTruePredicate
            , attributes = def
            }

test_baseStepRemainder :: [TestTree]
test_baseStepRemainder =
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
                [   ( StepResult
                        { rewrittenPattern = Predicated
                            { term = Mock.cg
                            , predicate = makeCeilPredicate Mock.cg
                            , substitution =
                                Substitution.wrap [(Mock.x, Mock.a)]
                            }
                        , remainder = Predicated
                            { term =
                                Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
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
                ]
        actual <- runSingleStepWithRemainder
            mockMetadataTools
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
                [   ( StepResult
                        { rewrittenPattern = Predicated
                            { term = Mock.cg
                            , predicate = makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeCeilPredicate Mock.cg)
                            , substitution = Substitution.wrap
                                [(Mock.x, Mock.a)]
                            }
                        , remainder = Predicated
                            { term =
                                Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                            , predicate = makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeNotPredicate
                                    (makeAndPredicate
                                        (makeCeilPredicate Mock.cg)
                                        (makeEqualsPredicate
                                            (mkVar Mock.x) Mock.a
                                        )
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
                ]
        actual <- runSingleStepWithRemainder
            mockMetadataTools
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
                [   ( StepResult
                        { rewrittenPattern = Predicated
                            { term = Mock.a
                            , predicate =
                                makeEqualsPredicate
                                    (Mock.f (mkVar Mock.x)) Mock.b
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
                ]
        actual <- runSingleStepWithRemainder
            mockMetadataTools
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

test_baseStepMultipleRemainder :: [TestTree]
test_baseStepMultipleRemainder =
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
            expected =
                OrStepResult
                    { rewrittenPattern = MultiOr.make
                        [ Predicated
                            { term = Mock.cg
                            , predicate = makeCeilPredicate Mock.cg
                            , substitution =
                                Substitution.wrap [(Mock.x, Mock.a)]
                            }
                        ]
                    , remainder = MultiOr.make
                        [ Predicated
                            { term =
                                Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                            , predicate =
                                makeNotPredicate
                                    (makeAndPredicate
                                        (makeCeilPredicate Mock.cg)
                                        (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                                    )
                            , substitution = mempty
                            }
                        ]
                    }
        actual <- runStepWithRemainders
            mockMetadataTools
            Predicated
                { term = Mock.functionalConstr20 (mkVar Mock.x) Mock.cg
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            [RewriteRule RulePattern
                { left =
                    Mock.functionalConstr20 Mock.a (mkVar Mock.y)
                , right = mkVar Mock.y
                , requires = makeTruePredicate
                , attributes = def
                }
            ]
        assertEqualWithExplanation "" expected actual
    , testCase "case" $ do
        -- This uses `functionalConstr30(x, y, z)` to represent a case
        -- statement,
        -- i.e. `case x of 1 -> y; 2 -> z`
        -- and `a`, `b` as the case labels.
        --
        -- Intended:
        --   term: case x of 1 -> cf; 2 -> cg
        --   axiom: case 1 of 1 -> cf; 2 -> cg => cf
        --   axiom: case 2 of 1 -> cf; 2 -> cg => cg
        -- Actual:
        --   term: constr30(x, cg, cf)
        --   axiom: constr30(a, y, z) => y
        --   axiom: constr30(b, y, z) => z
        -- Expected:
        --   rewritten: cf, with ⌈cf⌉ and ⌈cg⌉ and [x=a]
        --   rewritten:
        --      cg, with ¬(⌈cf⌉ and ⌈cg⌉ and x=b) and (⌈cf⌉ and ⌈cg⌉ and b=a)
        --   remainder:
        --     constr20(x, cf, cg)
        --        with ¬(⌈cf⌉ and ⌈cg⌉ and x=a)
        --        and ¬(⌈cf⌉ and ⌈cg⌉ and x=b)
        let
            unificationNotBottom =
                makeAndPredicate
                    (makeCeilPredicate Mock.cf)
                    (makeCeilPredicate Mock.cg)
            expected =
                OrStepResult
                    { rewrittenPattern = MultiOr.make
                        [ Predicated
                            { term = Mock.cf
                            , predicate = unificationNotBottom
                            , substitution =
                                Substitution.wrap [(Mock.x, Mock.a)]
                            }
                        , Predicated
                            { term = Mock.cg
                            , predicate = makeAndPredicate
                                (makeNotPredicate
                                    (makeAndPredicate
                                        unificationNotBottom
                                        (makeEqualsPredicate Mock.b Mock.a)
                                    )
                                )
                                unificationNotBottom
                            , substitution =
                                Substitution.wrap [(Mock.x, Mock.b)]
                            }
                        ]
                    , remainder = MultiOr.make
                        [ Predicated
                            { term =
                                Mock.functionalConstr30
                                    (mkVar Mock.x) Mock.cf Mock.cg
                            , predicate =
                                makeAndPredicate
                                    (makeNotPredicate
                                        (makeAndPredicate
                                            unificationNotBottom
                                            (makeEqualsPredicate
                                                (mkVar Mock.x)
                                                Mock.a
                                            )
                                        )
                                    )
                                    (makeNotPredicate
                                        (makeAndPredicate
                                            unificationNotBottom
                                            (makeEqualsPredicate
                                                (mkVar Mock.x)
                                                Mock.b
                                            )
                                        )
                                    )
                            , substitution = mempty
                            }
                        ]
                    }
        actual <- runStepWithRemainders
            mockMetadataTools
            Predicated
                { term =
                    Mock.functionalConstr30 (mkVar Mock.x) Mock.cf Mock.cg
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            [ RewriteRule RulePattern
                { left = Mock.functionalConstr30
                    Mock.a (mkVar Mock.y) (mkVar Mock.z)
                , right = mkVar Mock.y
                , requires = makeTruePredicate
                , attributes = def
                }
            , RewriteRule RulePattern
                { left = Mock.functionalConstr30
                    Mock.b (mkVar Mock.y) (mkVar Mock.z)
                , right = mkVar Mock.z
                , requires = makeTruePredicate
                , attributes = def
                }
            ]
        assertEqualWithExplanation "" expected actual
    ]

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

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools = MetadataTools
    { symAttributes = mockStepperAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = undefined
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    }

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

sigmaSymbol :: SymbolOrAlias Meta
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#sigma"
    , symbolOrAliasParams = []
    }

metaSigma
    :: CommonStepPattern Meta
    -> CommonStepPattern Meta
    -> CommonStepPattern Meta
metaSigma p1 p2 = mkApp patternMetaSort sigmaSymbol [p1, p2]


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#f"
    , symbolOrAliasParams = []
    }

metaF
    :: CommonStepPattern Meta
    -> CommonStepPattern Meta
metaF p = mkApp patternMetaSort fSymbol [p]


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#g"
    , symbolOrAliasParams = []
    }

metaG
    :: CommonStepPattern Meta
    -> CommonStepPattern Meta
metaG p = mkApp patternMetaSort gSymbol [p]

hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#h"
    , symbolOrAliasParams = []
    }

metaH
    :: CommonStepPattern Meta
    -> CommonStepPattern Meta
metaH p = mkApp patternMetaSort hSymbol [p]

iSymbol :: SymbolOrAlias Meta
iSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#i" AstLocationTest
    , symbolOrAliasParams = []
    }

metaI
    :: CommonStepPattern Meta
    -> CommonStepPattern Meta
metaI p = mkApp patternMetaSort iSymbol [p]

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> RewriteRule level Variable
    -> IO
        (Either
            (StepError level Variable)
            [(CommonExpandedPattern level, StepProof level Variable)]
        )
runStep metadataTools configuration axiom = do
    ioResult <-
        runSingleStepWithRemainder metadataTools configuration axiom
    return $ do
        results <- ioResult
        return (map processResult results)
  where
    processResult (StepResult { rewrittenPattern }, proof) =
        (rewrittenPattern, proof)

runStepWithRemainders
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [RewriteRule level Variable]
    -> IO (OrStepResult level Variable)
runStepWithRemainders metadataTools configuration axioms =
    fst
    <$> SMT.runSMT SMT.defaultConfig
            ( evalSimplifier emptyLogger
            $ stepWithRemainders
                metadataTools
                (Mock.substitutionSimplifier metadataTools)
                (Simplifier.create metadataTools Map.empty)
                Map.empty
                configuration
                axioms
            )

runSingleStepWithRemainder
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> RewriteRule level Variable
    -> IO
        (Either
            (StepError level Variable)
            [(StepResult level Variable, StepProof level Variable)]
        )
runSingleStepWithRemainder metadataTools configuration axiom =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ runExceptT
    $ stepWithRewriteRule
        metadataTools
        (Mock.substitutionSimplifier metadataTools)
        (Simplifier.create metadataTools Map.empty)
        Map.empty
        configuration
        axiom

instantiateRule
    :: RulePattern Object Variable
    -> PredicateSubstitution Object Variable
    -> IO
        (Either
            (StepError Object Variable)
            (MultiOr (UnifiedRule Variable))
        )
instantiateRule axiom unifier =
    evalUnifier
    $ BaseStep.instantiateRule
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        unifier { term = axiom }
  where
    metadataTools = mockMetadataTools
    predicateSimplifier =
        PredicateSubstitution.create
            metadataTools
            patternSimplifier
            axiomSimplifiers
    patternSimplifier =
        Simplifier.create
            metadataTools
            axiomSimplifiers
    axiomSimplifiers = Map.empty

evalUnifier
    :: BranchT (ExceptT e Simplifier) a
    -> IO (Either e (MultiOr a))
evalUnifier =
    SMT.runSMT SMT.defaultConfig
    . evalSimplifier emptyLogger
    . runExceptT
    . gather

test_instantiateRule :: [TestTree]
test_instantiateRule =
    [ testCase "substitute left-hand side" $ do
        let axiom =
                RulePattern
                    { left = mkVar Mock.x
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            unifier =
                PredicateSubstitution.top
                    { substitution = Substitution.wrap [(Mock.x, Mock.a)] }
            expect = Mock.a
        Right [ instantiated ] <- instantiateRule axiom unifier
        let Predicated { term = axiom' } = instantiated
            RulePattern { left = actual } = axiom'
        assertEqual "" expect actual

    , testCase "substitute right-hand side" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = mkVar Mock.y
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            unifier =
                PredicateSubstitution.top
                    { substitution = Substitution.wrap [(Mock.y, Mock.b)] }
            expect = Mock.b
        Right [ instantiated ] <- instantiateRule axiom unifier
        let Predicated { term = axiom' } = instantiated
            RulePattern { right = actual } = axiom'
        assertEqual "" expect actual

    , testCase "substitute requires clause" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires =
                        Predicate.makeCeilPredicate (Mock.f (mkVar Mock.x))
                    , attributes = Default.def
                    }
            unifier =
                PredicateSubstitution.top
                    { substitution = Substitution.wrap [(Mock.x, Mock.a)] }
            expect = Predicate.makeCeilPredicate (Mock.f Mock.a)
        Right [ instantiated ] <- instantiateRule axiom unifier
        let Predicated { term = axiom' } = instantiated
            RulePattern { requires = actual } = axiom'
        assertEqual "" expect actual

    , testCase "\\bottom unification condition" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            unifier = PredicateSubstitution.bottom
            expect = Right []
        actual <- instantiateRule axiom unifier
        assertEqual "" expect actual

    , testCase "conflicted unification" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            unifier =
                Predicated
                    { term = ()
                    , predicate =
                        Predicate.makeNotPredicate
                        $ Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
                    , substitution = Substitution.wrap [(Mock.x, Mock.a)]
                    }
            expect = Right []
        actual <- instantiateRule axiom unifier
        assertEqual "" expect actual

    , testCase "unification conflicts with requirement" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires =
                        Predicate.makeNotPredicate
                        $ Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
                    , attributes = Default.def
                    }
            unifier =
                PredicateSubstitution.top
                    { substitution = Substitution.wrap [(Mock.x, Mock.a)] }
            expect = Right []
        actual <- instantiateRule axiom unifier
        assertEqual "" expect actual

    , testCase "normalization failure" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            unifier =
                PredicateSubstitution.top
                    { substitution =
                        Substitution.wrap
                            [ (Mock.x, Mock.f (mkVar Mock.y))
                            , (Mock.y, mkVar Mock.x)
                            ]
                    }
        actual <- instantiateRule axiom unifier
        assertBool "" (Either.isLeft actual)

    , testCase "normalize substitution" $ do
        let axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            unifier =
                PredicateSubstitution.top
                    { substitution = Substitution.wrap [(Mock.x, Mock.a)] }
        Right [ instantiated ] <- instantiateRule axiom unifier
        let Predicated { substitution = actual } = instantiated
        assertBool "" (Substitution.isNormalized actual)

    -- Uncomment below when PredicateSubstitution simplifier branches.
    -- , testCase "branch on requirement" $ do
    --     let axiom =
    --             RulePattern
    --                 { left = Mock.a
    --                 , right = Mock.b
    --                 , requires = Predicate.makeOrPredicate expect1 expect2
    --                 , attributes = Default.def
    --                 }
    --         unifier = ExpandedPattern.topPredicate
    --         expect1 = Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
    --         expect2 = Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.b
    --     Right [ actual1, actual2 ] <- instantiateRule axiom unifier
    --     assertEqual "" expect1 (predicate actual1)
    --     assertEqual "" expect2 (predicate actual2)

    ]

applyRule
    :: PredicateSubstitution Object Variable
    -> UnifiedRule Variable
    -> IO
        (Either
            (StepError Object Variable)
            (MultiOr (ExpandedPattern Object Variable))
        )
applyRule initial instantiated =
    evalUnifier
    $ BaseStep.applyRule
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        initial
        instantiated
  where
    metadataTools = mockMetadataTools
    predicateSimplifier =
        PredicateSubstitution.create
            metadataTools
            patternSimplifier
            axiomSimplifiers
    patternSimplifier =
        Simplifier.create
            metadataTools
            axiomSimplifiers
    axiomSimplifiers = Map.empty

test_applyRule :: [TestTree]
test_applyRule =
    [ testCase "\\bottom initial condition" $ do
        let instantiated =
                Predicated
                    { term = axiom
                    , predicate = Predicate.makeTruePredicate
                    , substitution = mempty
                    }
            axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            initial = PredicateSubstitution.bottom
            expect = Right []
        actual <- applyRule initial instantiated
        assertEqual "" expect actual

    , testCase "returns axiom right-hand side" $ do
        let instantiated =
                Predicated
                    { term = axiom
                    , predicate = Predicate.makeTruePredicate
                    , substitution = mempty
                    }
            axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            initial = PredicateSubstitution.top
            expect = Right [ right axiom <$ initial ]
        actual <- applyRule initial instantiated
        assertEqual "" expect actual

    , testCase "combine initial and rule conditions" $ do
        let instantiated =
                Predicated
                    { term = axiom
                    , predicate = expect2
                    , substitution = mempty
                    }
            axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            initial = PredicateSubstitution.fromPredicate expect1
            expect1 =
                Predicate.makeEqualsPredicate
                    (Mock.f $ mkVar Mock.x)
                    Mock.a
            expect2 =
                Predicate.makeEqualsPredicate
                    (Mock.f $ mkVar Mock.y)
                    Mock.b
            expect = Predicate.makeAndPredicate expect1 expect2
        Right [ applied ] <- applyRule initial instantiated
        let Predicated { predicate = actual } = applied
        assertEqual "" expect actual

    , testCase "conflicting initial and rule conditions" $ do
        let predicate = Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
            instantiated =
                Predicated
                    { term = axiom
                    , predicate
                    , substitution = mempty
                    }
            axiom =
                RulePattern
                    { left = Mock.a
                    , right = Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            initial =
                PredicateSubstitution.fromPredicate
                $ Predicate.makeNotPredicate predicate
            expect = Right []
        actual <- applyRule initial instantiated
        assertEqual "" expect actual

    ]

unifyRule
    :: ExpandedPattern Object Variable
    -> RulePattern Object Variable
    -> IO
        (Either
            (StepError Object Variable)
            (MultiOr (Predicated Object Variable (RulePattern Object Variable)))
        )
unifyRule initial rule =
    evalUnifier
    $ BaseStep.unifyRule
        metadataTools
        unificationProcedure
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        initial
        rule
  where
    metadataTools = mockMetadataTools
    unificationProcedure = UnificationProcedure Unification.unificationProcedure
    predicateSimplifier =
        PredicateSubstitution.create
            metadataTools
            patternSimplifier
            axiomSimplifiers
    patternSimplifier =
        Simplifier.create
            metadataTools
            axiomSimplifiers
    axiomSimplifiers = Map.empty

test_unifyRule :: [TestTree]
test_unifyRule =
    [ testCase "renames axiom left variables" $ do
        let initial = pure (Mock.f (mkVar Mock.x))
            axiom =
                RulePattern
                    { left = Mock.f (mkVar Mock.x)
                    , right = Mock.g (mkVar Mock.x)
                    , requires =
                        Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a
                    , attributes = Default.def
                    }
        Right [unified] <- unifyRule initial axiom
        let Predicated { term = actual } = unified
        assertBool "" (Set.notMember Mock.x $ RulePattern.freeVariables actual)

    , testCase "performs unification with initial term" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr10 (mkVar Mock.x)
                    , right = Mock.g Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            expect = Right [(pure axiom) { substitution }]
              where
                substitution = Substitution.unsafeWrap [(Mock.x, Mock.a)]
        actual <- unifyRule initial axiom
        assertEqualWithExplanation "" expect actual

    , testCase "returns unification failures" $ do
        let initial = pure (Mock.functionalConstr10 Mock.a)
            axiom =
                RulePattern
                    { left = Mock.functionalConstr11 (mkVar Mock.x)
                    , right = Mock.g Mock.b
                    , requires = Predicate.makeTruePredicate
                    , attributes = Default.def
                    }
            expect = Right []
        actual <- unifyRule initial axiom
        assertEqualWithExplanation "" expect actual
    ]

stepWithRewriteRuleBranch
    :: ExpandedPattern Object Variable
    -> RewriteRule Object Variable
    -> IO
        (Either
            (StepError Object Variable)
            (MultiOr (ExpandedPattern Object Variable))
        )
stepWithRewriteRuleBranch initial rule =
    evalUnifier
    $ BaseStep.stepWithRewriteRuleBranch
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        initial
        rule
  where
    metadataTools = mockMetadataTools
    predicateSimplifier =
        PredicateSubstitution.create
            metadataTools
            patternSimplifier
            axiomSimplifiers
    patternSimplifier =
        Simplifier.create
            metadataTools
            axiomSimplifiers
    axiomSimplifiers = Map.empty

test_stepWithRewriteRuleBranch :: [TestTree]
test_stepWithRewriteRuleBranch =
    [ testCase "apply identity axiom" $ do
        let expect = Right [ initial ]
            initial = pure (mkVar Mock.x)
        actual <- stepWithRewriteRuleBranch initial axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "apply identity without renaming" $ do
        let expect = Right [ initial ]
            initial = pure (mkVar Mock.y)
        actual <- stepWithRewriteRuleBranch initial axiomId
        assertEqualWithExplanation "" expect actual

    , testCase "substitute variable with itself" $ do
        let expect = Right [ initial { term = mkVar Mock.x } ]
            initial = pure (Mock.sigma (mkVar Mock.x) (mkVar Mock.x))
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "merge configuration patterns" $ do
        let term = Mock.functionalConstr10 (mkVar Mock.y)
            expect =
                Right [ initial { term, substitution } ]
              where
                substitution = Substitution.wrap [ (Mock.x, term) ]
            initial = pure (Mock.sigma (mkVar Mock.x) term)
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "substitution with symbol matching" $ do
        let expect = Right [ initial { term = fz, substitution } ]
              where
                substitution = Substitution.wrap [ (Mock.y, mkVar Mock.z) ]
            fy = Mock.functionalConstr10 (mkVar Mock.y)
            fz = Mock.functionalConstr10 (mkVar Mock.z)
            initial = pure (Mock.sigma fy fz)
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "merge multiple variables" $ do
        let expect = Right [ initial { term = yy, substitution } ]
              where
                substitution = Substitution.wrap [ (Mock.x, mkVar Mock.y) ]
            xy = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            yx = Mock.sigma (mkVar Mock.y) (mkVar Mock.x)
            yy = Mock.sigma (mkVar Mock.y) (mkVar Mock.y)
            initial = pure (Mock.sigma xy yx)
        actual <- stepWithRewriteRuleBranch initial axiomSigmaSigma
        assertEqualWithExplanation "" expect actual

    , testCase "rename quantified right variables" $ do
        let expect = Right [ pure final ]
            final = mkExists (nextVariable Mock.y) (mkVar Mock.y)
            initial = pure (mkVar Mock.y)
            axiom =
                RewriteRule RulePattern
                    { left = mkVar Mock.x
                    , right = mkExists Mock.y (mkVar Mock.x)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
        actual <- stepWithRewriteRuleBranch initial axiom
        assertEqualWithExplanation "" expect actual

    , testCase "symbol clash" $ do
        let expect = Right []
            fx = Mock.functionalConstr10 (mkVar Mock.x)
            gy = Mock.functionalConstr11 (mkVar Mock.y)
            initial = pure (Mock.sigma fx gy)
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    , testCase "impossible substitution" $ do
        let expect = Right []
            xfy =
                Mock.sigma
                    (mkVar Mock.x)
                    (Mock.functionalConstr10 (mkVar Mock.y))
            xy = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            initial = pure (Mock.sigma xfy xy)
        actual <- stepWithRewriteRuleBranch initial axiomSigmaSigma
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, f(b)) with substitution b=a
    , testCase "impossible substitution (ctor)" $ do
        let expect = Right []
            initial =
                Predicated
                    { term =
                        Mock.sigma
                            (mkVar Mock.x)
                            (Mock.functionalConstr10 (mkVar Mock.y))
                    , predicate = Predicate.makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, mkVar Mock.x)]
                    }
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, h(b)) with substitution b=a
    , testCase "circular dependency error" $ do
        let expect =
                -- TODO(virgil): This should probably be a normal result with
                -- b=h(b) in the predicate.
                Left
                $ StepErrorSubstitution
                $ NonCtorCircularVariableDependency [Mock.y]
            initial =
                Predicated
                    { term =
                        Mock.sigma
                            (mkVar Mock.x)
                            (Mock.functional10 (mkVar Mock.y))
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(Mock.y, mkVar Mock.x)]
                    }
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- sigma(x, x) -> x
    -- vs
    -- sigma(a, i(b)) with substitution b=a
    , testCase "non-function substitution error" $ do
        let expect = Left $ StepErrorUnification UnsupportedPatterns
            initial =
                pure $ Mock.sigma (mkVar Mock.x) (Mock.plain10 (mkVar Mock.y))
        actual <- stepWithRewriteRuleBranch initial axiomSigmaId
        assertEqualWithExplanation "" expect actual

    -- -- sigma(x, x) -> x
    -- -- vs
    -- -- sigma(sigma(a, a), sigma(sigma(b, c), sigma(b, b)))
    -- , testCase "Unification is applied repeatedly" $ do
    --     let expect = Right
    --             [ Predicated
    --                 { term =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ c1 patternMetaSort)
    --                             (mkVar $ c1 patternMetaSort)
    --                         )
    --                         (metaSigma
    --                             (mkVar $ c1 patternMetaSort)
    --                             (mkVar $ c1 patternMetaSort)
    --                         )
    --                 , predicate = makeTruePredicate
    --                 , substitution = Substitution.wrap
    --                     [   ( a1 patternMetaSort
    --                         , metaSigma
    --                             (mkVar $ c1 patternMetaSort)
    --                             (mkVar $ c1 patternMetaSort)
    --                         )
    --                     ,   ( b1 patternMetaSort
    --                         , mkVar $ c1 patternMetaSort
    --                         )
    --                     ]
    --                 }
    --             ]
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ a1 patternMetaSort)
    --                             (mkVar $ a1 patternMetaSort)
    --                         )
    --                         (metaSigma
    --                             (metaSigma
    --                                 (mkVar $ b1 patternMetaSort)
    --                                 (mkVar $ c1 patternMetaSort)
    --                             )
    --                             (metaSigma
    --                                 (mkVar $ b1 patternMetaSort)
    --                                 (mkVar $ b1 patternMetaSort)
    --                             )
    --                         )
    --                 , predicate = makeTruePredicate
    --                 , substitution = mempty
    --                 }
    --             axiomMetaSigmaId
    --     assertEqualWithExplanation "" expect (fmap (map fst) actual)

    -- -- sigma(sigma(x, x), y) => sigma(x, y)
    -- -- vs
    -- -- sigma(sigma(a, f(b)), a)
    -- -- Expected: sigma(f(b), f(b)) and a=f(b)
    -- , testCase "Substitution normalization." $ do
    --     let
    --         fOfB = metaF (mkVar $ b1 patternMetaSort)
    --         expect = Right
    --             [   ( Predicated
    --                     { term = metaSigma fOfB fOfB
    --                     , predicate = makeTruePredicate
    --                     , substitution = Substitution.wrap
    --                         [(a1 patternMetaSort, fOfB)]
    --                     }
    --                 , mconcat
    --                     (map stepProof
    --                         [ StepProofVariableRenamings []
    --                         , StepProofUnification EmptyUnificationProof
    --                         ]
    --                     )
    --                 )
    --             ]
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ a1 patternMetaSort)
    --                             fOfB
    --                         )
    --                         (mkVar $ a1 patternMetaSort)
    --                 , predicate = makeTruePredicate
    --                 , substitution = mempty
    --                 }
    --             (RewriteRule RulePattern
    --                 { left =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ x1 patternMetaSort)
    --                             (mkVar $ x1 patternMetaSort)
    --                         )
    --                         (mkVar $ y1 patternMetaSort)
    --                 , right =
    --                     metaSigma
    --                         (mkVar $ x1 patternMetaSort)
    --                         (mkVar $ y1 patternMetaSort)
    --                 , requires = makeTruePredicate
    --                 , attributes = def
    --                 }
    --             )
    --     assertEqualWithExplanation "" expect actual

    -- -- sigma(sigma(x, x), y) => sigma(x, y)
    -- -- vs
    -- -- sigma(sigma(a, f(b)), a) and a=f(c)
    -- -- Expected: sigma(f(b), f(b)) and a=f(b), b=c
    -- , testCase "Merging substitution with existing one." $ do
    --     let
    --         fOfB = metaF (mkVar $ b1 patternMetaSort)
    --         fOfC = metaF (mkVar $ c1 patternMetaSort)
    --         expect = Right
    --             [   ( Predicated
    --                     { term = metaSigma fOfC fOfC
    --                     , predicate = makeTruePredicate
    --                     , substitution = Substitution.wrap
    --                         [ (a1 patternMetaSort, fOfC)
    --                         , (b1 patternMetaSort, mkVar $ c1 patternMetaSort)
    --                         ]
    --                     }
    --                 , mconcat
    --                     (map stepProof
    --                         [ StepProofVariableRenamings []
    --                         , StepProofUnification EmptyUnificationProof
    --                         ]
    --                     )
    --                 )
    --             ]
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term =
    --                     metaSigma
    --                         (metaSigma (mkVar $ a1 patternMetaSort) fOfB)
    --                         (mkVar $ a1 patternMetaSort)
    --                 , predicate = makeTruePredicate
    --                 , substitution = Substitution.wrap
    --                     [(a1 patternMetaSort, fOfC)]
    --                 }
    --             (RewriteRule RulePattern
    --                 { left =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ x1 patternMetaSort)
    --                             (mkVar $ x1 patternMetaSort)
    --                         )
    --                         (mkVar $ y1 patternMetaSort)
    --                 , right =
    --                     metaSigma
    --                         (mkVar $ x1 patternMetaSort)
    --                         (mkVar $ y1 patternMetaSort)
    --                 , requires = makeTruePredicate
    --                 , attributes = def
    --                 }
    --             )
    --     assertEqualWithExplanation "" expect actual

    -- -- "sl1" => x
    -- -- vs
    -- -- "sl2"
    -- -- Expected: bottom
    -- , testCase "Matching different string literals is bottom" $ do
    --     let expect = Right []
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term = mkStringLiteral "sl2"
    --                 , predicate = makeTruePredicate
    --                 , substitution = mempty
    --                 }
    --             (RewriteRule RulePattern
    --                 { left = mkStringLiteral "sl1"
    --                 , right = mkVar $ x1 patternMetaSort
    --                 , requires = makeTruePredicate
    --                 , attributes = def
    --                 }
    --             )
    --     assertEqualWithExplanation "" expect (fmap (map fst) actual)

    -- -- x => x
    -- -- vs
    -- -- a and g(a)=f(a)
    -- -- Expected: y1 and g(a)=f(a)
    -- , testCase "Preserving initial condition." $ do
    --     let expect = Right
    --             [   ( Predicated
    --                     { term = mkVar $ a1 patternMetaSort
    --                     , predicate =
    --                         makeEqualsPredicate
    --                             (metaG (mkVar $ a1 patternMetaSort))
    --                             (metaF (mkVar $ a1 patternMetaSort))
    --                     , substitution = mempty
    --                     }
    --                 , mconcat
    --                     (map stepProof
    --                         [ StepProofVariableRenamings []
    --                         , StepProofUnification EmptyUnificationProof
    --                         ]
    --                     )
    --                 )
    --             ]
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term = mkVar $ a1 patternMetaSort
    --                 , predicate =
    --                     makeEqualsPredicate
    --                         (metaG (mkVar $ a1 patternMetaSort))
    --                         (metaF (mkVar $ a1 patternMetaSort))
    --                 , substitution = mempty
    --                 }
    --             axiomId
    --     assertEqualWithExplanation "" expect actual

    -- -- sigma(sigma(x, x), y) => sigma(x, y)
    -- -- vs
    -- -- sigma(sigma(a, f(b)), a) and g(a)=f(a)
    -- -- Expected: sigma(f(b), f(b)) and a=f(b) and and g(f(b))=f(f(b))
    -- , testCase "Substitution_normalization." $ do
    --     let
    --         fOfB = metaF (mkVar $ b1 patternMetaSort)
    --         expect = Right
    --             [   ( Predicated
    --                     { term = metaSigma fOfB fOfB
    --                     , predicate =
    --                         makeEqualsPredicate (metaG fOfB) (metaF fOfB)
    --                     , substitution = Substitution.wrap
    --                         [(a1 patternMetaSort, fOfB)]
    --                     }
    --                 , mconcat
    --                     (map stepProof
    --                         [ StepProofVariableRenamings []
    --                         , StepProofUnification EmptyUnificationProof
    --                         ]
    --                     )
    --                 )
    --             ]
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ a1 patternMetaSort)
    --                             fOfB
    --                         )
    --                         (mkVar $ a1 patternMetaSort)
    --                 , predicate =
    --                     makeEqualsPredicate
    --                         (metaG (mkVar $ a1 patternMetaSort))
    --                         (metaF (mkVar $ a1 patternMetaSort))
    --                 , substitution = mempty
    --                 }
    --             (RewriteRule RulePattern
    --                 { left =
    --                     metaSigma
    --                         (metaSigma
    --                             (mkVar $ x1 patternMetaSort)
    --                             (mkVar $ x1 patternMetaSort)
    --                         )
    --                         (mkVar $ y1 patternMetaSort)
    --                 , right =
    --                     metaSigma
    --                         (mkVar $ x1 patternMetaSort)
    --                         (mkVar $ y1 patternMetaSort)
    --                 , requires = makeTruePredicate
    --                 , attributes = def
    --                 }
    --             )
    --     assertEqualWithExplanation "" expect actual

    -- -- x => x requires g(x)=f(x)
    -- -- vs
    -- -- a
    -- -- Expected: y1 and g(a)=f(a)
    -- , testCase "Conjoins axiom pre-condition" $ do
    --     let
    --         preCondition var =
    --             makeEqualsPredicate
    --                 (metaG (mkVar $ var patternMetaSort))
    --                 (metaF (mkVar $ var patternMetaSort))
    --         expect = Right
    --             [   ( Predicated
    --                     { term = mkVar $ a1 patternMetaSort
    --                     , predicate = preCondition a1
    --                     , substitution = mempty
    --                     }
    --                 , mconcat
    --                     (map stepProof
    --                         [ StepProofVariableRenamings []
    --                         , StepProofUnification EmptyUnificationProof
    --                         ]
    --                     )
    --                 )
    --             ]
    --     actual <-
    --         runStep
    --             mockMetaMetadataTools
    --             Predicated
    --                 { term = mkVar $ a1 patternMetaSort
    --                 , predicate = makeTruePredicate
    --                 , substitution = mempty
    --                 }
    --             (RewriteRule ruleId { requires = preCondition x1 })
    --     assertEqualWithExplanation "" expect actual
    ]
  where
    ruleId =
        RulePattern
            { left = mkVar Mock.x
            , right = mkVar Mock.x
            , requires = makeTruePredicate
            , attributes = def
            }
    axiomId = RewriteRule ruleId

    axiomSigmaId =
        RewriteRule RulePattern
            { left = Mock.sigma (mkVar Mock.x) (mkVar Mock.x)
            , right = mkVar Mock.x
            , requires = makeTruePredicate
            , attributes = def
            }

    axiomSigmaSigma =
        RewriteRule RulePattern
            { left =
                Mock.sigma
                    (Mock.sigma
                        (mkVar Mock.x)
                        (mkVar Mock.x)
                    )
                    (Mock.sigma
                        (mkVar Mock.y)
                        (mkVar Mock.y)
                    )
            , right = Mock.sigma (mkVar Mock.x) (mkVar Mock.y)
            , requires = makeTruePredicate
            , attributes = def
            }
