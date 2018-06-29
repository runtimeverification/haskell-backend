{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Step.Function.IntegrationTest (functionIntegrationTests) where

import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import qualified Data.Map                              as Map


import           Test.Tasty                            (TestTree, testGroup)
import           Test.Tasty.HUnit                      (testCase)

import           Data.Kore.AST.Common                  (Application (..),
                                                        AstLocation (..),
                                                        Id (..), Pattern (..),
                                                        Sort,
                                                        SymbolOrAlias (..))
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML                  (CommonPurePattern)
import           Data.Kore.AST.PureToKore              (patternKoreToPure)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Comparators                 ()
import           Data.Kore.MetaML.AST                  (CommonMetaPattern)
import           Data.Kore.Step.BaseStep               (AxiomPattern (..))
import           Data.Kore.Step.Condition.Condition    (ConditionSort (..),
                                                        EvaluatedCondition (..))
import           Data.Kore.Step.Function.Data          (ApplicationFunctionEvaluator (..),
                                                        AttemptedFunctionResult (..),
                                                        CommonPurePatternFunctionEvaluator,
                                                        ConditionEvaluator,
                                                        FunctionResult (..),
                                                        FunctionResultProof (..))
import           Data.Kore.Step.Function.Evaluator     (evaluateFunctions)
import           Data.Kore.Step.Function.UserDefined   (axiomFunctionEvaluator)
import           Data.Kore.Variables.Fresh.IntCounter  (IntCounter,
                                                        runIntCounter)

import           Test.Tasty.HUnit.Extensions

functionIntegrationTests :: TestTree
functionIntegrationTests =
    testGroup
        "Function evaluation integration tests"
        [ testCase "Simple evaluation"
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern = asPureMetaPattern (metaG metaC)
                    , functionResultCondition = ConditionTrue
                    }
                (evaluate
                    mockMetadataTools
                    (Map.singleton fId
                        [ axiomEvaluator
                            (conditionSort SortSort)
                            (asPureMetaPattern (metaF (v1 PatternSort)))
                            (asPureMetaPattern (metaG (v1 PatternSort)))
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern (metaF metaC))
                )
            )
        , testCase "Evaluates inside functions"
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern =
                        asPureMetaPattern (metaG (metaG metaC))
                    , functionResultCondition = ConditionTrue
                    }
                (evaluate
                    mockMetadataTools
                    (Map.singleton fId
                        [ axiomEvaluator
                            (conditionSort SortSort)
                            (asPureMetaPattern (metaF (v1 PatternSort)))
                            (asPureMetaPattern (metaG (v1 PatternSort)))
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern (metaF (metaF metaC)))
                )
            )
        , testCase "Does not evaluate with 'or' - may chage in the future"
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern = asPureMetaPattern
                        (metaF (metaOr PatternSort (metaF metaC) (metaF metaC)))
                    , functionResultCondition = ConditionTrue
                    }
                (evaluate
                    mockMetadataTools
                    (Map.singleton fId
                        [ axiomEvaluator
                            (conditionSort SortSort)
                            (asPureMetaPattern (metaF (v1 PatternSort)))
                            (asPureMetaPattern (metaG (v1 PatternSort)))
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern
                        (metaF (metaOr PatternSort (metaF metaC) (metaF metaC)))
                    )
                )
            )
        , testCase "Evaluates on multiple branches"
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern = asPureMetaPattern
                        (metaG (metaSigma (metaG metaC) (metaG metaC)))
                    , functionResultCondition = ConditionTrue
                    }
                (evaluate
                    mockMetadataTools
                    (Map.singleton fId
                        [ axiomEvaluator
                            (conditionSort SortSort)
                            (asPureMetaPattern (metaF (v1 PatternSort)))
                            (asPureMetaPattern (metaG (v1 PatternSort)))
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern
                        (metaF (metaSigma (metaF metaC) (metaF metaC)))
                    )
                )
            )
        , testCase "Returns conditions"
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern = asPureMetaPattern (metaF metaD)
                    , functionResultCondition = conditionUnevaluable metaC
                    }
                (evaluate
                    mockMetadataTools
                    (Map.singleton cId
                        [ appliedMockEvaluator FunctionResult
                            { functionResultPattern   = asPureMetaPattern metaD
                            , functionResultCondition =
                                conditionUnevaluable metaC
                            }
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern (metaF metaC))
                )
            )
        , testCase "Merges conditions"
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern =
                        asPureMetaPattern (metaG (metaSigma metaE metaE))
                    , functionResultCondition =
                        conditionUnevaluable
                            (metaAnd SortSort
                                (metaCeil
                                    (ResultSort SortSort) PatternSort metaC
                                )
                                (metaCeil
                                    (ResultSort SortSort) PatternSort metaD
                                )
                            )
                    }
                (evaluate
                    mockMetadataTools
                    (Map.fromList
                        [   ( cId
                            ,   [ appliedMockEvaluator FunctionResult
                                    { functionResultPattern   =
                                        asPureMetaPattern metaE
                                    , functionResultCondition =
                                        conditionUnevaluable
                                            (metaCeil
                                                (ResultSort SortSort)
                                                PatternSort
                                                metaC)
                                    }
                                ]
                            )
                        ,   ( dId
                            ,   [ appliedMockEvaluator FunctionResult
                                    { functionResultPattern   =
                                        asPureMetaPattern metaE
                                    , functionResultCondition =
                                        conditionUnevaluable
                                            (metaCeil
                                                (ResultSort SortSort)
                                                PatternSort
                                                metaD)
                                    }
                                ]
                            )
                        ,   (fId
                            ,   [ axiomEvaluator
                                    (conditionSort SortSort)
                                    (asPureMetaPattern (metaF (v1 PatternSort)))
                                    (asPureMetaPattern (metaG (v1 PatternSort)))
                                ]
                            )
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern (metaF (metaSigma metaC metaD)))
                )
            )
        , testCase "Reevaluates user-defined function results."
            (assertEqualWithExplanation ""
                FunctionResult
                    { functionResultPattern = asPureMetaPattern (metaF metaE)
                    , functionResultCondition = conditionUnevaluable metaD
                    }
                (evaluate
                    mockMetadataTools
                    (Map.fromList
                        [   ( cId
                            ,   [ axiomEvaluator
                                    (conditionSort SortSort)
                                    (asPureMetaPattern metaC)
                                    (asPureMetaPattern metaD)
                                ]
                            )
                        ,   ( dId
                            ,   [ appliedMockEvaluator FunctionResult
                                    { functionResultPattern   =
                                        asPureMetaPattern metaE
                                    , functionResultCondition =
                                        conditionUnevaluable metaD
                                    }
                                ]
                            )
                        ]
                    )
                    (conditionSort SortSort)
                    (asPureMetaPattern (metaF metaC))
                )
            )
        ]

axiomEvaluator
    :: ConditionSort Meta
    -> CommonPurePattern Meta
    -> CommonPurePattern Meta
    -> ApplicationFunctionEvaluator Meta
axiomEvaluator sort left right =
    ApplicationFunctionEvaluator
        (axiomFunctionEvaluator
            mockMetadataTools
            sort
            AxiomPattern
                { axiomPatternLeft  = left
                , axiomPatternRight = right
                }
        )

conditionSort :: AsAst (Sort level) s => s -> ConditionSort level
conditionSort sort = ConditionSort (asAst sort)

appliedMockEvaluator
    :: FunctionResult level -> ApplicationFunctionEvaluator level
appliedMockEvaluator result =
    ApplicationFunctionEvaluator (mockEvaluator (Applied result))

mockEvaluator
    :: AttemptedFunctionResult level
    -> ConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Application level (CommonPurePattern level)
    -> IntCounter (AttemptedFunctionResult level, FunctionResultProof level)
mockEvaluator evaluation _ _ _ =
    return (evaluation, FunctionResultProof)

evaluate
    :: MetadataTools level
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -> ConditionSort level
    -> CommonPurePattern level
    -> FunctionResult level
evaluate metadataTools functionIdToEvaluator conditionSort' patt =
    fst $ fst
        (runIntCounter
            (evaluateFunctions
                metadataTools functionIdToEvaluator conditionSort' patt
            )
            0
        )

v1 :: MetaSort sort => sort -> MetaVariable sort
v1 = metaVariable "#v1" AstLocationTest

conditionUnevaluable
    :: ProperPattern Meta sort patt => patt -> EvaluatedCondition Meta
conditionUnevaluable patt =
    ConditionUnevaluable (asPureMetaPattern patt)

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
asPureMetaPattern patt = patternKoreToPure Meta (asAst patt)

mockMetadataTools :: MetadataTools Meta
mockMetadataTools = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , isFunction = const True
    , getArgumentSorts = const [asAst PatternSort, asAst PatternSort]
    , getResultSort = const (asAst PatternSort)
    }

fId :: Id Meta
fId = Id "#f" AstLocationTest

fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = fId
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

gId :: Id Meta
gId = Id "#g" AstLocationTest

gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = gId
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

cId :: Id Meta
cId = Id "#c" AstLocationTest

cSymbol :: SymbolOrAlias Meta
cSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cId
    , symbolOrAliasParams = []
    }

data MetaC = MetaC

instance ProperPattern Meta PatternSort MetaC
  where
    asProperPattern MetaC =
        ApplicationPattern Application
            { applicationSymbolOrAlias = cSymbol
            , applicationChildren = []
            }
metaC :: MetaC
metaC = MetaC

dId :: Id Meta
dId = Id "#d" AstLocationTest

dSymbol :: SymbolOrAlias Meta
dSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = dId
    , symbolOrAliasParams = []
    }

data MetaD = MetaD

instance ProperPattern Meta PatternSort MetaD
  where
    asProperPattern MetaD =
        ApplicationPattern Application
            { applicationSymbolOrAlias = dSymbol
            , applicationChildren = []
            }
metaD :: MetaD
metaD = MetaD

eId :: Id Meta
eId = Id "#e" AstLocationTest

eSymbol :: SymbolOrAlias Meta
eSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = eId
    , symbolOrAliasParams = []
    }

data MetaE = MetaE

instance ProperPattern Meta PatternSort MetaE
  where
    asProperPattern MetaE =
        ApplicationPattern Application
            { applicationSymbolOrAlias = eSymbol
            , applicationChildren = []
            }
metaE :: MetaE
metaE = MetaE

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
