module Test.Kore.Step.Function.UserDefined (test_userDefinedFunction) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import           Data.List
                 ( sort )
import qualified Data.Set as Set

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate
                 ( makeFalsePredicate, makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), bottom )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.Function.Data
                 ( CommonAttemptedFunction )
import           Kore.Step.Function.UserDefined
                 ( ruleFunctionEvaluator )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( CommonStepPatternSimplifier, SimplificationProof (..),
                 evalSimplifier )
import           Kore.Step.StepperAttributes
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.Simplifier
                 ( mockSimplifier )
import           Test.Tasty.HUnit.Extensions

test_userDefinedFunction :: [TestTree]
test_userDefinedFunction =
    [ testCase "Applies one step" $ do
        let expect =
                AttemptedFunction.Applied $ OrOfExpandedPattern.make
                    [ Predicated
                        { term =
                            asApplicationPattern $ metaG (mkVar $ x patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluateWithAxiom
                mockMetadataTools
                (EqualityRule RulePattern
                    { left =
                        asApplicationPattern $ metaF (mkVar $ x patternMetaSort)
                    , right =
                        asApplicationPattern $ metaG (mkVar $ x patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier [])
                (metaF (mkVar $ x patternMetaSort))
        assertEqualWithExplanation "f(x) => g(x)" [expect] actual

    , testCase "Cannot apply step with unsat axiom pre-condition" $ do
        let expect =
                AttemptedFunction.Applied (OrOfExpandedPattern.make [])
        actual <-
            evaluateWithAxiom
                mockMetadataTools
                (EqualityRule RulePattern
                    { left =
                        asApplicationPattern $ metaF (mkVar $ x patternMetaSort)
                    , right =
                        asApplicationPattern $ metaG (mkVar $ x patternMetaSort)
                    , requires = makeFalsePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier [])
                (metaF (mkVar $ x patternMetaSort))
        assertEqualWithExplanation "f(x) => g(x) requires false" [expect] actual

    , testCase "Cannot apply step with unsat condition" $ do
        let expect =
                AttemptedFunction.Applied
                $ OrOfExpandedPattern.make [ ExpandedPattern.bottom ]
        actual <-
            evaluateWithAxiom
                mockMetadataTools
                (EqualityRule RulePattern
                    { left =
                        asApplicationPattern $ metaF (mkVar $ x patternMetaSort)
                    , right =
                        asApplicationPattern $ metaG (mkVar $ x patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier
                    -- Evaluate Top to Bottom.
                    [ (mkTop_, ([], SimplificationProof)) ]
                )
                (metaF (mkVar $ x patternMetaSort))
        assertEqualWithExplanation "" [expect] actual

    , testCase "Preserves step substitution" $ do
        let expect =
                AttemptedFunction.Applied $ OrOfExpandedPattern.make
                    [ Predicated
                        { term =
                            asApplicationPattern $ metaG (mkVar $ b patternMetaSort)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [(a patternMetaSort, mkVar $ b patternMetaSort)]
                        }
                    ]
        actual <-
            evaluateWithAxiom
                mockMetadataTools
                (EqualityRule RulePattern
                    { left  =
                        asApplicationPattern $ metaSigma
                            (mkVar $ x patternMetaSort)
                            (mkVar $ x patternMetaSort)
                    , right =
                        asApplicationPattern $ metaG (mkVar $ x patternMetaSort)
                    , requires = makeTruePredicate
                    , attributes = def
                    }
                )
                (mockSimplifier [])
                (metaSigma
                    (mkVar $ a patternMetaSort)
                    (mkVar $ b patternMetaSort)
                )
        assertEqualWithExplanation "sigma(x,x) => g(x) vs sigma(a, b)"
            [expect]
            actual

    -- TODO: Add a test for StepWithAxiom returning a condition.
    -- TODO: Add a test for the stepper giving up
    ]

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.constructorFunctionalAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = const Mock.constructorFunctionalAttributes
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    }

x, a, b :: Sort Meta -> Variable Meta
x = Variable (testId "#x")
a = Variable (testId "#a")
b = Variable (testId "#b")

fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#f"
    , symbolOrAliasParams = []
    }

metaF
    :: CommonStepPattern Meta
    -> CofreeF
        (Application Meta)
        (Valid (Variable Meta) Meta)
        (CommonStepPattern Meta)
metaF p =
    valid :< Application fSymbol [p]
  where
    Valid { freeVariables } = extract p
    valid = Valid { patternSort = patternMetaSort, freeVariables }


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#g"
    , symbolOrAliasParams = []
    }

metaG
    :: CommonStepPattern Meta
    -> CofreeF
        (Application Meta)
        (Valid (Variable Meta) Meta)
        (CommonStepPattern Meta)
metaG p =
    valid :< Application gSymbol [p]
  where
    Valid { freeVariables } = extract p
    valid = Valid { patternSort = patternMetaSort, freeVariables }

sigmaSymbol :: SymbolOrAlias Meta
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = testId "#sigma"
    , symbolOrAliasParams = []
    }

metaSigma
    :: CommonStepPattern Meta
    -> CommonStepPattern Meta
    -> CofreeF
        (Application Meta)
        (Valid (Variable Meta) Meta)
        (CommonStepPattern Meta)
metaSigma p1 p2 =
    valid :< Application sigmaSymbol [p1, p2]
  where
    Valid { freeVariables = freeVariables1 } = extract p1
    Valid { freeVariables = freeVariables2 } = extract p2
    freeVariables = Set.union freeVariables1 freeVariables2
    valid = Valid { patternSort = patternMetaSort, freeVariables }

asApplicationPattern
    :: CofreeF
        (Application Meta)
        (Valid (Variable Meta) Meta)
        (CommonStepPattern Meta)
    -> CommonStepPattern Meta
asApplicationPattern (valid :< app) =
    asPurePattern (valid :< ApplicationPattern app)

evaluateWithAxiom
    :: forall level . MetaOrObject level
    => MetadataTools level StepperAttributes
    -> EqualityRule level
    -> CommonStepPatternSimplifier level
    -> CofreeF
        (Application level)
        (Valid (Variable level) level)
        (CommonStepPattern level)
    -> IO [CommonAttemptedFunction level]
evaluateWithAxiom
    metadataTools
    axiom
    simplifier
    app
  = do
    results <- evaluated
    return (map normalizeResult results)
  where
    normalizeResult
        :: CommonAttemptedFunction level -> CommonAttemptedFunction level
    normalizeResult =
        \case
            AttemptedFunction.Applied orPattern ->
                AttemptedFunction.Applied (fmap sortSubstitution orPattern)
            result -> result

    sortSubstitution Predicated {term, predicate, substitution} =
        Predicated
            { term = term
            , predicate = predicate
            , substitution = Substitution.modify sort substitution
            }
    evaluated :: IO [CommonAttemptedFunction level]
    evaluated =
        (<$>) (map fst)
        $ SMT.runSMT SMT.defaultConfig
        $ evalSimplifier
        $ ruleFunctionEvaluator
            axiom
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
            app
