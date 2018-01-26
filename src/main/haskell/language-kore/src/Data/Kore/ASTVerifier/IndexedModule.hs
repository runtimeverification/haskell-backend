module Data.Kore.ASTVerifier.IndexedModule
    (implicitIndexedModule, indexModule) where

import           Data.Kore.AST
import qualified Data.Map as Map
import qualified Data.Set as Set

implicitIndexedModule :: ModuleName -> (IndexedModule, Set.Set String)
implicitIndexedModule name =
    ( IndexedModule
        { indexedModuleName = name
        , indexedModuleMetaAliasSentences = Map.empty
        , indexedModuleObjectAliasSentences = Map.empty
        , indexedModuleMetaSymbolSentences = Map.empty
        , indexedModuleObjectSymbolSentences = Map.empty
        , indexedModuleObjectSortDescriptions = Map.empty
        , indexedModuleMetaSortDescriptions = metaSortDescriptions
        , indexedModuleAxioms = []
        , indexedModuleAttributes = Attributes []
        }
    , Set.map getId (Map.keysSet metaSortDescriptions)
    )

metaSortDescriptions :: Map.Map (Id Meta) (SortDescription Meta)
metaSortDescriptions = Map.fromList (map metaSortDescription metaSortsList)

metaSortDescription :: MetaSortType -> (Id Meta, SortDescription Meta)
metaSortDescription sortType =
    ( sortId
    , SortDescription
        { sortDescriptionName = sortId
        , sortDescriptionParameters = []
        , sortDescriptionAttributes = Attributes []
        }
    )
  where
    sortId = Id (show sortType)

indexModule :: Module -> IndexedModule -> IndexedModule
indexModule koreModule defaultIndexedModule =
    foldl indexModuleSentence indexedModule (moduleSentences koreModule)
  where
    indexedModule =
        defaultIndexedModule
            { indexedModuleName = moduleName koreModule
            , indexedModuleAttributes = moduleAttributes koreModule
            }

indexModuleSentence
    :: IndexedModule -> Sentence -> IndexedModule
indexModuleSentence
    indexedModule @ IndexedModule
        { indexedModuleMetaAliasSentences = sentences }
    (MetaSentenceAliasSentence sentence)
  =
    indexedModule
        { indexedModuleMetaAliasSentences =
            Map.insert
                (aliasConstructor (sentenceAliasAlias sentence))
                sentence
                sentences
        }
indexModuleSentence
    indexedModule @ IndexedModule
        { indexedModuleObjectAliasSentences = sentences }
    (ObjectSentenceAliasSentence sentence)
  =
    indexedModule
        { indexedModuleObjectAliasSentences =
            Map.insert
                (aliasConstructor (sentenceAliasAlias sentence))
                sentence
                sentences
        }
indexModuleSentence
    indexedModule @ IndexedModule
        { indexedModuleMetaSymbolSentences = sentences }
    (MetaSentenceSymbolSentence sentence)
  =
    indexedModule
        { indexedModuleMetaSymbolSentences =
            Map.insert
                (symbolConstructor (sentenceSymbolSymbol sentence))
                sentence
                sentences
        }
indexModuleSentence
    indexedModule @ IndexedModule
        { indexedModuleObjectSymbolSentences = sentences }
    (ObjectSentenceSymbolSentence sentence)
  =
    indexedModule
        { indexedModuleObjectSymbolSentences =
            Map.insert
                (symbolConstructor (sentenceSymbolSymbol sentence))
                sentence
                sentences
        }
indexModuleSentence
    indexedModule @ IndexedModule
        { indexedModuleObjectSortDescriptions = descriptions }
    (SentenceSortSentence sentence)
  =
    indexedModule
        { indexedModuleObjectSortDescriptions =
            Map.insert
                (sentenceSortName sentence)
                (toSortDescription sentence)
                descriptions
        }
indexModuleSentence
    indexedModule @ IndexedModule { indexedModuleAxioms = sentences }
    (SentenceAxiomSentence sentence)
  =
    indexedModule { indexedModuleAxioms = sentence : sentences }

toSortDescription :: SentenceSort -> SortDescription Object
toSortDescription sentence = SortDescription
    { sortDescriptionName = sentenceSortName sentence
    , sortDescriptionParameters = sentenceSortParameters sentence
    , sortDescriptionAttributes = sentenceSortAttributes sentence
    }
