module Test.Data.Kore.Step.Function.UserDefined (test_userDefinedFunction) where

import           Test.Tasty                            (TestTree)
import           Test.Tasty.HUnit                      (testCase)

import           Test.Data.Kore.Comparators            ()
import           Test.Data.Kore.Step.Condition         (mockConditionEvaluator)
import           Test.Data.Kore.Step.Function          (mockFunctionEvaluator)

import           Data.Kore.AST.Common                  (Application (..),
                                                        AstLocation (..),
                                                        Id (..), Pattern (..),
                                                        Sort (..),
                                                        SymbolOrAlias (..))
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML                  (CommonPurePattern,
                                                        fromPurePattern)
import           Data.Kore.AST.PureToKore              (patternKoreToPure)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Error
import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import           Data.Kore.MetaML.AST                  (CommonMetaPattern)
import           Data.Kore.Step.BaseStep               (AxiomPattern (..))
import           Data.Kore.Step.Condition.Condition    (ConditionProof (..),
                                                        ConditionSort (..),
                                                        EvaluatedCondition (..),
                                                        UnevaluatedCondition (..))
import           Data.Kore.Step.Function.Data          (AttemptedFunctionResult (..),
                                                        CommonPurePatternFunctionEvaluator (..),
                                                        ConditionEvaluator (..),
                                                        FunctionResult (..),
                                                        FunctionResultProof (..))
import           Data.Kore.Step.Function.UserDefined   (axiomFunctionEvaluator)
import           Data.Kore.Variables.Fresh.IntCounter

import           Test.Tasty.HUnit.Extensions

test_userDefinedFunction :: [TestTree]
test_userDefinedFunction =
    [ testCase "Cannot apply function if step fails"
        (assertEqualWithExplanation ""
            AttemptedFunctionResultNotApplicable
            (evaluateWithAxiom
                mockMetadataTools
                (ConditionSort sortSort)
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    }
                (mockConditionEvaluator [])
                (mockFunctionEvaluator [])
                (asApplication (metaH (x PatternSort)))
            )
        )
    , testCase "Applies one step"
        (assertEqualWithExplanation "f(x) => g(x)"
            (AttemptedFunctionResultApplied FunctionResult
                { functionResultPattern   =
                    asPureMetaPattern (metaG (x PatternSort))
                , functionResultCondition = ConditionTrue
                }
            )
            (evaluateWithAxiom
                mockMetadataTools
                (ConditionSort sortSort)
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    }
                (mockConditionEvaluator
                    [   ( unevaluatedCondition
                            (metaAnd SortSort
                                (metaTop SortSort)
                                (metaTop SortSort)
                            )
                        , (ConditionTrue, ConditionProof)
                        )
                    ]
                )
                (mockFunctionEvaluator [])
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Cannot apply step with unsat condition"
        (assertEqualWithExplanation ""
            AttemptedFunctionResultNotApplicable
            (evaluateWithAxiom
                mockMetadataTools
                (ConditionSort sortSort)
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    }
                (mockConditionEvaluator
                    [   ( unevaluatedCondition
                            (metaAnd SortSort
                                (metaTop SortSort)
                                (metaTop SortSort)
                            )
                        , (ConditionFalse, ConditionProof)
                        )
                    ]
                )
                (mockFunctionEvaluator [])
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Reevaluates the step application"
        (assertEqualWithExplanation "f(x) => g(x) and g(x) => h(x)"
            (AttemptedFunctionResultApplied FunctionResult
                { functionResultPattern   =
                    asPureMetaPattern (metaH (x PatternSort))
                , functionResultCondition = ConditionTrue
                }
            )
            (evaluateWithAxiom
                mockMetadataTools
                (ConditionSort sortSort)
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    }
                (mockConditionEvaluator
                    [   ( unevaluatedCondition
                            (metaAnd SortSort
                                (metaTop SortSort)
                                (metaTop SortSort)
                            )
                        , (ConditionTrue, ConditionProof)
                        )
                    ]
                )
                (mockFunctionEvaluator
                    [   ( asPureMetaPattern (metaG (x PatternSort))
                        ,   ( FunctionResult
                                { functionResultPattern =
                                    asPureMetaPattern
                                        (metaH (x PatternSort))
                                , functionResultCondition =
                                    ConditionTrue
                                }
                            , FunctionResultProof
                            )
                        )
                    ]
                )
                (asApplication (metaF (x PatternSort)))
            )
        )
    , testCase "Does not reevaluate the step application with incompatible condition"
        (assertEqualWithExplanation "f(x) => g(x) and g(x) => h(x) + false"
            (AttemptedFunctionResultApplied FunctionResult
                { functionResultPattern   =
                    asPureMetaPattern (metaG (x PatternSort))
                , functionResultCondition = ConditionTrue
                }
            )
            (evaluateWithAxiom
                mockMetadataTools
                (ConditionSort sortSort)
                AxiomPattern
                    { axiomPatternLeft  =
                        asPureMetaPattern (metaF (x PatternSort))
                    , axiomPatternRight =
                        asPureMetaPattern (metaG (x PatternSort))
                    }
                (mockConditionEvaluator
                    [   ( unevaluatedCondition
                            (metaAnd SortSort
                                (metaTop SortSort)
                                (metaTop SortSort)
                            )
                        , (ConditionTrue, ConditionProof)
                        )
                    ]
                )
                (mockFunctionEvaluator
                    [   ( asPureMetaPattern (metaG (x PatternSort))
                        ,   ( FunctionResult
                                { functionResultPattern =
                                    asPureMetaPattern
                                        (metaH (x PatternSort))
                                , functionResultCondition =
                                    ConditionFalse
                                }
                            , FunctionResultProof
                            )
                        )
                    ]
                )
                (asApplication (metaF (x PatternSort)))
            )
        )
    ]

mockMetadataTools :: MetadataTools Meta
mockMetadataTools = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , isFunction = const False
    , getArgumentSorts = const [asAst PatternSort, asAst PatternSort]
    , getResultSort = const (asAst PatternSort)
    }

x :: MetaSort sort => sort -> MetaVariable sort
x = metaVariable "#x" AstLocationTest

sortSort :: Sort Meta
sortSort = asAst SortSort


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

unevaluatedCondition
    :: ProperPattern Meta sort patt => patt -> UnevaluatedCondition Meta
unevaluatedCondition patt =
    UnevaluatedCondition (asPureMetaPattern patt)

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
        ApplicationPattern a -> a
        _                    -> error "Expected an Application pattern."

evaluateWithAxiom
    :: MetaOrObject level
    => MetadataTools level
    -> ConditionSort level
    -> AxiomPattern level
    -> ConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Application level (CommonPurePattern level)
    -> AttemptedFunctionResult level
evaluateWithAxiom
    metadataTools
    conditionSort
    axiom
    conditionEvaluator
    functionEvaluator
    app
  =
    fst $ fst $ runIntCounter
        (axiomFunctionEvaluator
            metadataTools
            conditionSort
            axiom
            conditionEvaluator
            functionEvaluator
            app
        )
        0
