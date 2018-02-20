module Data.Kore.ASTVerifier.IndexedModule
    (implicitIndexedModule, indexModule) where

import           Data.Kore.AST
import qualified Data.Map      as Map
import qualified Data.Set      as Set

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
    foldr
        indexModuleSentence
        defaultIndexedModule
            { indexedModuleName = moduleName koreModule
            , indexedModuleAttributes = moduleAttributes koreModule
            }
        (moduleSentences koreModule)

indexModuleSentence
    :: Sentence -> IndexedModule -> IndexedModule
indexModuleSentence
    (MetaSentenceAliasSentence sentence)
    indexedModule @ IndexedModule
        { indexedModuleMetaAliasSentences = sentences }
  =
    indexedModule
        { indexedModuleMetaAliasSentences =
            Map.insert
                (aliasConstructor (sentenceAliasAlias sentence))
                sentence
                sentences
        }
indexModuleSentence
    (ObjectSentenceAliasSentence sentence)
    indexedModule @ IndexedModule
        { indexedModuleObjectAliasSentences = sentences }
  =
    indexedModule
        { indexedModuleObjectAliasSentences =
            Map.insert
                (aliasConstructor (sentenceAliasAlias sentence))
                sentence
                sentences
        }
indexModuleSentence
    (MetaSentenceSymbolSentence sentence)
    indexedModule @ IndexedModule
        { indexedModuleMetaSymbolSentences = sentences }
  =
    indexedModule
        { indexedModuleMetaSymbolSentences =
            Map.insert
                (symbolConstructor (sentenceSymbolSymbol sentence))
                sentence
                sentences
        }
indexModuleSentence
    (ObjectSentenceSymbolSentence sentence)
    indexedModule @ IndexedModule
        { indexedModuleObjectSymbolSentences = sentences }
  =
    indexedModule
        { indexedModuleObjectSymbolSentences =
            Map.insert
                (symbolConstructor (sentenceSymbolSymbol sentence))
                sentence
                sentences
        }
indexModuleSentence
    (SentenceSortSentence sentence)
    indexedModule @ IndexedModule
        { indexedModuleObjectSortDescriptions = descriptions }
  =
    indexedModule
        { indexedModuleObjectSortDescriptions =
            Map.insert
                (sentenceSortName sentence)
                (toSortDescription sentence)
                descriptions
        }
indexModuleSentence
    (SentenceAxiomSentence sentence)
    indexedModule @ IndexedModule { indexedModuleAxioms = sentences }
  =
    indexedModule { indexedModuleAxioms = sentence : sentences }

-- TODO(virgil): Replace sort description with SentenceSort (Meta/Object)
toSortDescription :: SentenceSort -> SortDescription Object
toSortDescription sentence = SortDescription
    { sortDescriptionName = sentenceSortName sentence
    , sortDescriptionParameters = sentenceSortParameters sentence
    , sortDescriptionAttributes = sentenceSortAttributes sentence
    }
