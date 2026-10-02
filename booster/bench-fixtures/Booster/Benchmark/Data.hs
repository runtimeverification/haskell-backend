{-# LANGUAGE OverloadedRecordDot #-}

{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Benchmark fixtures and synthetic data for booster benchmark suites.
-}
module Booster.Benchmark.Data (
    benchmarkSizes,
    benchmarkDefinition,
    benchmarkKMapDef,
    benchmarkKSetDef,
    benchmarkKListDef,
    mkMapTerm,
    mkMapWithValueVariables,
    mkMapWithKeyVariables,
    mkPatternMapForMatch,
    mkSubjectMapForMatch,
    mkValueSubstitution,
    mkKeySubstitution,
    mkLookupExistingKey,
    mkLookupMissingKey,
    mkInsertKey,
    mkUpdatedValue,
    mkListTerm,
    mkListConcatRhs,
    mkSetTerm,
    mkMapKey,
    mkMapValue,
    mkListElement,
    mkSetElement,
    pipelinePatternTerm,
    pipelineSubjectTerm,
    pipelineRhsTerm,
    validateKMap,
    validateKSet,
    validateKList,
) where

import Data.ByteString.Char8 qualified as BS
import Data.Map qualified as Map
import Data.Set qualified as Set

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.Base

benchmarkSizes :: [Int]
benchmarkSizes = [10, 100, 1000, 5000, 10000, 50000]

benchmarkKMapDef :: KMapDefinition
benchmarkKMapDef =
    KMapDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'BenchMap"
                , elementSymbolName = "LblBenchMapItem"
                , concatSymbolName = "Lbl'Unds'BenchMap'Unds'"
                }
        , keySortName = "SortBenchMapKey"
        , elementSortName = "SortBenchMapItem"
        , mapSortName = "SortBenchMap"
        }

benchmarkKListDef :: KListDefinition
benchmarkKListDef =
    KListDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'BenchList"
                , elementSymbolName = "LblBenchListItem"
                , concatSymbolName = "Lbl'Unds'BenchList'Unds'"
                }
        , elementSortName = "SortBenchListItem"
        , listSortName = "SortBenchList"
        }

benchmarkKSetDef :: KSetDefinition
benchmarkKSetDef =
    KListDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'BenchSet"
                , elementSymbolName = "LblBenchSetItem"
                , concatSymbolName = "Lbl'Unds'BenchSet'Unds'"
                }
        , elementSortName = "SortBenchSetItem"
        , listSortName = "SortBenchSet"
        }

mapKeySort, mapValueSort, listElementSort, setElementSort, pipelineSort :: Sort
mapKeySort = SortApp benchmarkKMapDef.keySortName []
mapValueSort = SortApp benchmarkKMapDef.elementSortName []
listElementSort = SortApp benchmarkKListDef.elementSortName []
setElementSort = SortApp benchmarkKSetDef.elementSortName []
pipelineSort = SortApp "SortBenchTerm" []

mkMapKey :: Int -> Term
mkMapKey n = DomainValue mapKeySort (BS.pack ("key-" <> show n))

mkMapValue :: Int -> Term
mkMapValue n = DomainValue mapValueSort (BS.pack ("value-" <> show n))

mkListElement :: Int -> Term
mkListElement n = DomainValue listElementSort (BS.pack ("list-" <> show n))

mkSetElement :: Int -> Term
mkSetElement n = DomainValue setElementSort (BS.pack ("set-" <> show n))

mkMapTerm :: Int -> Term
mkMapTerm size =
    KMap
        benchmarkKMapDef
        [ (mkMapKey ix, mkMapValue ix)
        | ix <- [1 .. max 0 size]
        ]
        Nothing

mkMapWithValueVariables :: Int -> Term
mkMapWithValueVariables size =
    KMap
        benchmarkKMapDef
        [ (mkMapKey ix, Var (valueVariable ix))
        | ix <- [1 .. max 0 size]
        ]
        Nothing

mkMapWithKeyVariables :: Int -> Term
mkMapWithKeyVariables size =
    KMap
        benchmarkKMapDef
        [ (Var (keyVariable ix), mkMapValue ix)
        | ix <- [1 .. max 0 size]
        ]
        Nothing

mkPatternMapForMatch :: Int -> Term
mkPatternMapForMatch size =
    KMap
        benchmarkKMapDef
        [ (mkMapKey ix, Var (matchValueVariable ix))
        | ix <- [1 .. max 0 size]
        ]
        Nothing

mkSubjectMapForMatch :: Int -> Term
mkSubjectMapForMatch = mkMapTerm

mkValueSubstitution :: Int -> Substitution
mkValueSubstitution size =
    Map.fromList
        [ (valueVariable ix, mkUpdatedValue (size + ix))
        | ix <- [1 .. max 0 size]
        ]

mkKeySubstitution :: Int -> Substitution
mkKeySubstitution size =
    Map.fromList
        [ (keyVariable ix, mkMapKey (size + ix))
        | ix <- [1 .. max 0 size]
        ]

mkLookupExistingKey :: Int -> Term
mkLookupExistingKey size = mkMapKey (max 1 (size `div` 2))

mkLookupMissingKey :: Int -> Term
mkLookupMissingKey size =
    DomainValue mapKeySort (BS.pack ("missing-" <> show (max 0 size)))

mkInsertKey :: Int -> Term
mkInsertKey size =
    DomainValue mapKeySort (BS.pack ("insert-" <> show (max 0 size)))

mkUpdatedValue :: Int -> Term
mkUpdatedValue size =
    DomainValue mapValueSort (BS.pack ("updated-" <> show (max 0 size)))

mkListTerm :: Int -> Term
mkListTerm size =
    KList
        benchmarkKListDef
        [ mkListElement ix
        | ix <- [1 .. max 0 size]
        ]
        Nothing

mkListConcatRhs :: Int -> Term
mkListConcatRhs size =
    let safe = max 0 size
     in KList
            benchmarkKListDef
            [ mkListElement ix
            | ix <- [safe + 1 .. (2 * safe)]
            ]
            Nothing

mkSetTerm :: Int -> Term
mkSetTerm size =
    KSet
        benchmarkKSetDef
        [ mkSetElement ix
        | ix <- [1 .. max 0 size]
        ]
        Nothing

pipelineVariable :: Variable
pipelineVariable =
    Variable
        { variableSort = pipelineSort
        , variableName = "PIPELINE_X"
        }

pipelinePatternTerm :: Term
pipelinePatternTerm =
    SymbolApplication benchConstructorSymbol [] [Var pipelineVariable]

pipelineSubjectTerm :: Term
pipelineSubjectTerm =
    SymbolApplication
        benchConstructorSymbol
        []
        [DomainValue pipelineSort "subject"]

pipelineRhsTerm :: Term
pipelineRhsTerm =
    SymbolApplication benchFunctionSymbol [] [Var pipelineVariable]

benchmarkDefinition :: KoreDefinition
benchmarkDefinition =
    (emptyKoreDefinition defaultDefAttributes)
        { modules = Map.singleton "BENCH" ModuleAttributes
        , sorts = Map.fromList (map mkSortDecl allSortNames)
        , symbols =
            Map.fromList
                [ (benchConstructorSymbol.name, benchConstructorSymbol)
                , (benchFunctionSymbol.name, benchFunctionSymbol)
                ]
        }
  where
    allSortNames =
        [ benchmarkKMapDef.keySortName
        , benchmarkKMapDef.elementSortName
        , benchmarkKMapDef.mapSortName
        , benchmarkKListDef.elementSortName
        , benchmarkKListDef.listSortName
        , benchmarkKSetDef.elementSortName
        , benchmarkKSetDef.listSortName
        , "SortInt"
        , "SortBool"
        , "SortBenchTerm"
        ]

mkSortDecl :: SortName -> (SortName, (SortAttributes, Set.Set SortName))
mkSortDecl sortName =
    ( sortName
    ,
        ( SortAttributes
            { argCount = 0
            , collectionAttributes = Nothing
            }
        , Set.singleton sortName
        )
    )

mkSymbolAttributes :: SymbolType -> SymbolAttributes
mkSymbolAttributes symbolType =
    SymbolAttributes
        { symbolType
        , isIdem = IsNotIdem
        , isAssoc = IsNotAssoc
        , isMacroOrAlias = IsNotMacroOrAlias
        , hasEvaluators = CanBeEvaluated
        , collectionMetadata = Nothing
        , smt = Nothing
        , hook = Nothing
        }

benchConstructorSymbol :: Symbol
benchConstructorSymbol =
    Symbol
        { name = "benchCon"
        , sortVars = []
        , argSorts = [pipelineSort]
        , resultSort = pipelineSort
        , attributes = mkSymbolAttributes Constructor
        }

benchFunctionSymbol :: Symbol
benchFunctionSymbol =
    Symbol
        { name = "benchFn"
        , sortVars = []
        , argSorts = [pipelineSort]
        , resultSort = pipelineSort
        , attributes = mkSymbolAttributes (Function Total)
        }

valueVariable :: Int -> Variable
valueVariable ix =
    Variable
        { variableSort = mapValueSort
        , variableName = BS.pack ("V" <> show ix)
        }

keyVariable :: Int -> Variable
keyVariable ix =
    Variable
        { variableSort = mapKeySort
        , variableName = BS.pack ("K" <> show ix)
        }

matchValueVariable :: Int -> Variable
matchValueVariable ix =
    Variable
        { variableSort = mapValueSort
        , variableName = BS.pack ("MV" <> show ix)
        }

validateKMap :: Term -> Bool
validateKMap (KMap def keyVals Nothing) =
    def == benchmarkKMapDef
        && hasUniqueKeys keyVals
validateKMap _ = False

validateKSet :: Term -> Bool
validateKSet (KSet def elements Nothing) =
    def == benchmarkKSetDef
        && elements == sortAndDeduplicate elements
validateKSet _ = False

validateKList :: Term -> Bool
validateKList (KList def _ Nothing) = def == benchmarkKListDef
validateKList _ = False

hasUniqueKeys :: [(Term, Term)] -> Bool
hasUniqueKeys keyVals =
    let keys = map fst keyVals
     in length keys == Set.size (Set.fromList keys)
