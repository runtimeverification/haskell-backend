module Test.Kore.Step.Function.Integration (test_functionIntegration) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map
import           Data.Reflection
                 ( give )

import Kore.AST.Common
       ( Application (..), AstLocation (..), Id (..), Pattern (..),
       SymbolOrAlias (..) )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( CommonPurePattern )
import Kore.AST.PureToKore
       ( patternKoreToPure )
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.Building.AsAst
import Kore.Building.Patterns
import Kore.Building.Sorts
import Kore.Error
       ( printError )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..), SortTools )
import Kore.MetaML.AST
       ( CommonMetaPattern )
import Kore.Predicate.Predicate
       ( CommonPredicate, makeAndPredicate, makeCeilPredicate,
       makeEqualsPredicate, makeTruePredicate )
import Kore.Step.BaseStep
       ( AxiomPattern (..) )
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( CommonExpandedPattern, ExpandedPattern (..) )
import Kore.Step.Function.Data
       ( ApplicationFunctionEvaluator (..), CommonApplicationFunctionEvaluator,
       CommonAttemptedFunction, CommonConditionEvaluator,
       CommonPurePatternFunctionEvaluator, FunctionResultProof (..) )
import Kore.Step.Function.Data as AttemptedFunction
       ( AttemptedFunction (..) )
import Kore.Step.Function.Evaluator
       ( evaluateFunctions )
import Kore.Step.Function.UserDefined
       ( axiomFunctionEvaluator )
import Kore.Step.StepperAttributes
import Kore.Variables.Fresh.IntCounter
       ( IntCounter, runIntCounter )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_functionIntegration :: [TestTree]
test_functionIntegration =
    [ testCase "Simple evaluation"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = asPureMetaPattern (metaG metaC)
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton fId
                    [ axiomEvaluator
                        (asPureMetaPattern (metaF (v1 PatternSort)))
                        (asPureMetaPattern (metaG (v1 PatternSort)))
                    ]
                )
                (asPureMetaPattern (metaF metaC))
            )
        )
    , testCase "Evaluates inside functions"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term =
                    asPureMetaPattern (metaG (metaG metaC))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton fId
                    [ axiomEvaluator
                        (asPureMetaPattern (metaF (v1 PatternSort)))
                        (asPureMetaPattern (metaG (v1 PatternSort)))
                    ]
                )
                (asPureMetaPattern (metaF (metaF metaC)))
            )
        )
    , testCase "Does not evaluate with 'or' - may chage in the future"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = asPureMetaPattern
                    (metaF (metaOr PatternSort (metaF metaC) (metaF metaC)))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton fId
                    [ axiomEvaluator
                        (asPureMetaPattern (metaF (v1 PatternSort)))
                        (asPureMetaPattern (metaG (v1 PatternSort)))
                    ]
                )
                (asPureMetaPattern
                    (metaF (metaOr PatternSort (metaF metaC) (metaF metaC)))
                )
            )
        )
    , testCase "Evaluates on multiple branches"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = asPureMetaPattern
                    (metaG (metaSigma (metaG metaC) (metaG metaC)))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton fId
                    [ axiomEvaluator
                        (asPureMetaPattern (metaF (v1 PatternSort)))
                        (asPureMetaPattern (metaG (v1 PatternSort)))
                    ]
                )
                (asPureMetaPattern
                    (metaF (metaSigma (metaF metaC) (metaF metaC)))
                )
            )
        )
    , testCase "Returns conditions"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = asPureMetaPattern (metaF metaD)
                , predicate = makeCeil metaC
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.singleton cId
                    [ appliedMockEvaluator ExpandedPattern
                        { term   = asPureMetaPattern metaD
                        , predicate = makeCeil metaC
                        , substitution = []
                        }
                    ]
                )
                (asPureMetaPattern (metaF metaC))
            )
        )
    , testCase "Merges conditions"
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = asPureMetaPattern (metaG (metaSigma metaE metaE))
                , predicate = makeAnd (makeCeil metaC) (makeCeil metaD)
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( cId
                        ,   [ appliedMockEvaluator ExpandedPattern
                                { term = asPureMetaPattern metaE
                                , predicate = makeCeil metaC
                                , substitution = []
                                }
                            ]
                        )
                    ,   ( dId
                        ,   [ appliedMockEvaluator ExpandedPattern
                                { term = asPureMetaPattern metaE
                                , predicate = makeCeil metaD
                                , substitution = []
                                }
                            ]
                        )
                    ,   (fId
                        ,   [ axiomEvaluator
                                (asPureMetaPattern (metaF (v1 PatternSort)))
                                (asPureMetaPattern (metaG (v1 PatternSort)))
                            ]
                        )
                    ]
                )
                (asPureMetaPattern (metaF (metaSigma metaC metaD)))
            )
        )
    , testCase "Reevaluates user-defined function results."
        (assertEqualWithExplanation ""
            ExpandedPattern
                { term = asPureMetaPattern (metaF metaE)
                , predicate = makeEquals (metaF metaE) metaE
                , substitution = []
                }
            (evaluate
                mockMetadataTools
                (Map.fromList
                    [   ( cId
                        ,   [ axiomEvaluator
                                (asPureMetaPattern metaC)
                                (asPureMetaPattern metaD)
                            ]
                        )
                    ,   ( dId
                        ,   [ appliedMockEvaluator ExpandedPattern
                                { term = asPureMetaPattern metaE
                                , predicate = makeEquals (metaF metaE) metaE
                                , substitution = []
                                }
                            ]
                        )
                    ]
                )
                (asPureMetaPattern (metaF metaC))
            )
        )
    ]


axiomEvaluator
    :: CommonPurePattern Meta
    -> CommonPurePattern Meta
    -> CommonApplicationFunctionEvaluator Meta
axiomEvaluator left right =
    ApplicationFunctionEvaluator
        (axiomFunctionEvaluator
            AxiomPattern
                { axiomPatternLeft  = left
                , axiomPatternRight = right
                , axiomPatternRequires = makeTruePredicate
                }
        )

appliedMockEvaluator
    :: CommonExpandedPattern level -> CommonApplicationFunctionEvaluator level
appliedMockEvaluator result =
    ApplicationFunctionEvaluator
        (mockEvaluator (AttemptedFunction.Applied result))

mockEvaluator
    :: CommonAttemptedFunction level
    -> MetadataTools level StepperAttributes
    -> CommonConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Application level (CommonPurePattern level)
    -> IntCounter (CommonAttemptedFunction level, FunctionResultProof level)
mockEvaluator evaluation _ _ _ _ =
    return (evaluation, FunctionResultProof)

evaluate
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level]
    -> CommonPurePattern level
    -> CommonExpandedPattern level
evaluate metadataTools functionIdToEvaluator patt =
    fst $ fst
        (runIntCounter
            (evaluateFunctions metadataTools functionIdToEvaluator patt)
            0
        )

v1 :: MetaSort sort => sort -> MetaVariable sort
v1 = metaVariable "#v1" AstLocationTest

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

makeCeil
    :: ProperPattern Meta sort patt
    => patt -> CommonPredicate Meta
makeCeil patt =
    give (sortTools mockMetadataTools)
        (makeCeilPredicate (asPureMetaPattern patt))

makeAnd :: CommonPredicate Meta -> CommonPredicate Meta -> CommonPredicate Meta
makeAnd p1 p2 =
    give (sortTools mockMetadataTools) (fst $ makeAndPredicate p1 p2)

mockSortTools :: SortTools Meta
mockSortTools = const
    ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = (asAst PatternSort)
    }


mockStepperAttributes :: StepperAttributes
mockStepperAttributes = StepperAttributes
    { isConstructor = True
    , isFunctional = True
    , isFunction = True
    , hook = def
    }

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { attributes = const mockStepperAttributes
    , sortTools = mockSortTools
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
