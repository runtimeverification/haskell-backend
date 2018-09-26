module Test.Kore.Step.Function.UserDefined (test_userDefinedFunction) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Default
       ( def )
import Data.List
       ( sort )

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

import           Kore.AST.Common
                 ( Application (..), AstLocation (..), Id (..), Pattern (..),
                 SymbolOrAlias (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern, fromPurePattern )
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkTop )
import           Kore.Building.AsAst
import           Kore.Building.Patterns
import           Kore.Building.Sorts
import           Kore.Error
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SortTools )
import           Kore.MetaML.AST
                 ( CommonMetaPattern )
import           Kore.Predicate.Predicate
                 ( makeFalsePredicate, makeTruePredicate )
import           Kore.Step.BaseStep
                 ( AxiomPattern (..) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.Function.Data
                 ( CommonAttemptedFunction )
import           Kore.Step.Function.UserDefined
                 ( axiomFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier, SimplificationProof (..),
                 evalSimplifier )
import           Kore.Step.StepperAttributes

import Test.Kore.Comparators ()
import Test.Kore.Step.Simplifier
       ( mockSimplifier )

import Test.Tasty.HUnit.Extensions

test_userDefinedFunction :: [TestTree]
test_userDefinedFunction =
    [ testCase "Cannot apply function if step fails"
        (assertEqualWithExplanation ""
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkBottom
                    , predicate = makeFalsePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier [])
                (asApplication (metaH (x PatternSort)))
            )
        )
    , testCase "Applies one step"
        (assertEqualWithExplanation "f(x) => g(x)"
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = asPureMetaPattern (metaG (x PatternSort))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier [])
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Cannot apply step with unsat axiom pre-condition"
        (assertEqualWithExplanation "f(x) => g(x) requires false"
            (AttemptedFunction.Applied (OrOfExpandedPattern.make []))
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeFalsePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier [])
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Cannot apply step with unsat condition"
        (assertEqualWithExplanation ""
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ ExpandedPattern.bottom ]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier
                    -- Evaluate Top to Bottom.
                    [ (mkTop, ([], SimplificationProof)) ]
                )
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Reevaluates the step application"
        (assertEqualWithExplanation "f(x) => g(x) and g(x) => h(x)"
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = asPureMetaPattern (metaH (x PatternSort))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier
                    [   ( asPureMetaPattern (metaG (x PatternSort))
                        ,   (   [ ExpandedPattern
                                    { term =
                                        asPureMetaPattern (metaH (x PatternSort))
                                    , predicate = makeTruePredicate
                                    , substitution = []
                                    }
                                ]
                            , SimplificationProof
                            )
                        )
                    ]
                )
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Does not reevaluate the step application with incompatible condition"
        (assertEqualWithExplanation "f(x) => g(x) and g(x) => h(x) + false"
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ExpandedPattern.bottom]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier
                    [   ( asPureMetaPattern (metaG (x PatternSort))
                        ,   (   [ ExpandedPattern
                                    { term =
                                        asPureMetaPattern (metaH (x PatternSort))
                                    , predicate = makeFalsePredicate
                                    , substitution = []
                                    }
                                ]
                            , SimplificationProof
                            )
                        )
                    ]
                )
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Preserves step substitution"
        (assertEqualWithExplanation "sigma(x,x) => g(x) vs sigma(a, b)"
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = asPureMetaPattern (metaG (b PatternSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( asVariable (a PatternSort)
                            , asPureMetaPattern (b PatternSort)
                            )
                        ]
                    }
                ]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern
                            (metaSigma (x PatternSort) (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier [])
                (asApplication (metaSigma (a PatternSort) (b PatternSort)))
            )
        )
    , testCase "Merges the step substitution with the reevaluation one"
        (assertEqualWithExplanation
            "sigma(x,x) => g(x) vs sigma(a, b) and g(b) => h(c) + a=c,b=c"
            (AttemptedFunction.Applied $ OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = asPureMetaPattern (metaH (c PatternSort))
                    , predicate = makeTruePredicate
                    , substitution =
                        [   ( asVariable (a PatternSort)
                            -- TODO(virgil): Do we want normalization here?
                            , asPureMetaPattern (c PatternSort)
                            )
                        ,   ( asVariable (b PatternSort)
                            , asPureMetaPattern (c PatternSort)
                            )
                        ]
                    }
                ]
            )
            (evaluateWithAxiom
                mockMetadataTools
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern
                            (metaSigma (x PatternSort) (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    , axiomPatternRequires = makeTruePredicate
                    , axiomPatternAttributes = def
                    }
                (mockSimplifier
                    [   ( asPureMetaPattern (metaG (b PatternSort))
                        ,   (   [ ExpandedPattern
                                    { term =
                                        asPureMetaPattern (metaH (c PatternSort))
                                    , predicate = makeTruePredicate
                                    , substitution =
                                        [   ( asVariable (b PatternSort)
                                            , asPureMetaPattern (c PatternSort)
                                            )
                                        ]
                                    }
                                ]
                            , SimplificationProof
                            )
                        )
                    ]
                )
                (asApplication (metaSigma (a PatternSort) (b PatternSort)))
            )
        )
    -- TODO: Add a test for StepWithAxiom returning a condition.
    -- TODO: Add a test for the stepper giving up
    ]

mockSortTools :: SortTools Meta
mockSortTools = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.constructorFunctionalAttributes
    , sortAttributes = const Mock.constructorFunctionalAttributes
    , sortTools  = mockSortTools
    , isSubsortOf = const $ const False
    }

x :: MetaSort sort => sort -> MetaVariable sort
x = metaVariable "#x" AstLocationTest

a :: MetaSort sort => sort -> MetaVariable sort
a = metaVariable "#a" AstLocationTest

b :: MetaSort sort => sort -> MetaVariable sort
b = metaVariable "#b" AstLocationTest

c :: MetaSort sort => sort -> MetaVariable sort
c = metaVariable "#c" AstLocationTest

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

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
asPureMetaPattern patt =
    case patternKoreToPure Meta (asAst patt) of
        Left err  -> error (printError err)
        Right pat -> pat

asApplication
    :: ProperPattern Meta sort patt => patt
    -> Application Meta (CommonPurePattern Meta)
asApplication patt =
    case fromPurePattern (asPureMetaPattern patt) of
        ApplicationPattern app -> app
        _                      -> error "Expected an Application pattern."

evaluateWithAxiom
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> AxiomPattern level
    -> CommonPureMLPatternSimplifier level
    -> Application level (CommonPurePattern level)
    -> CommonAttemptedFunction level
evaluateWithAxiom
    metadataTools
    axiom
    simplifier
    app
  =
    case evaluated of
        AttemptedFunction.Applied orPattern ->
            AttemptedFunction.Applied (fmap sortSubstitution orPattern)
        result -> result
  where
    sortSubstitution ExpandedPattern {term, predicate, substitution} =
        ExpandedPattern
            { term = term
            , predicate = predicate
            , substitution = sort substitution
            }
    evaluated =
        fst
            $ evalSimplifier
            $ axiomFunctionEvaluator
                axiom
                metadataTools
                simplifier
                app
