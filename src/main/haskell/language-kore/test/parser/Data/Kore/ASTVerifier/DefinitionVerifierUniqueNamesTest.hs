module Data.Kore.ASTVerifier.DefinitionVerifierUniqueNamesTest
    (definitionVerifierUniqueNamesTests) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Data.Kore.AST.Common
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error

definitionVerifierUniqueNamesTests :: TestTree
definitionVerifierUniqueNamesTests =
    testGroup
        "Definition verifier - unique names - unit tests"
        [ expectSuccess "Simplest definition"
            (simpleDefinitionFromSentences (ModuleName "MODULE") [])
        , expectSuccess "Definition with sort"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleSortSentence (SortName "s") ]
            )
        , expectSuccess "Definition with meta alias"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#a") stringSortName ]
            )
        , expectSuccess "Definition with object alias"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectAliasSentence (AliasName "a") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Definition with meta symbol"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaSymbolSentence (SymbolName "#a") stringSortName ]
            )
        , expectSuccess "Definition with object symbol"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectSymbolSentence (SymbolName "a") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Definition with two sorts"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleSortSentence (SortName "s1")
                , simpleSortSentence (SortName "s2")
                ]
            )
        , expectSuccess "Definition with two meta aliases"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#a1") stringSortName
                , simpleMetaAliasSentence (AliasName "#a2") stringSortName
                ]
            )
        , expectSuccess "Definition with two object aliases"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectAliasSentence (AliasName "a1") (SortName "s")
                , simpleObjectAliasSentence (AliasName "a2") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Definition with two meta symbols"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#a1") stringSortName
                , simpleMetaAliasSentence (AliasName "#a2") stringSortName
                ]
            )
        , expectSuccess "Definition with two object symbols"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectSymbolSentence (SymbolName "a1") (SortName "s")
                , simpleObjectSymbolSentence (SymbolName "a2") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError "Definition with two identical sort names."
            (Error ["module 'MODULE'"] "Duplicated name: 's'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleSortSentence (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Definition with two identical meta alias names"
            (Error ["module 'MODULE'"] "Duplicated name: '#a'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#a") stringSortName
                , simpleMetaAliasSentence (AliasName "#a") stringSortName
                ]
            )
        , expectFailureWithError
            "Definition with two identical object alias names"
            (Error ["module 'MODULE'"] "Duplicated name: 'a'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectAliasSentence (AliasName "a") (SortName "s")
                , simpleObjectAliasSentence (AliasName "a") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Definition with two identical meta symbol names"
            (Error ["module 'MODULE'"] "Duplicated name: '#a'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#a") stringSortName
                , simpleMetaAliasSentence (AliasName "#a") stringSortName
                ]
            )
        , expectFailureWithError
            "Definition with two identical object symbol names"
            (Error ["module 'MODULE'"] "Duplicated name: 'a'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectSymbolSentence (SymbolName "a") (SortName "s")
                , simpleObjectSymbolSentence (SymbolName "a") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Definition with meta alias with same name as sort"
            (Error ["module 'MODULE'"] "Duplicated name: '#String'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#String") stringSortName ]
            )
        , expectFailureWithError
            "Definition with object alias with same name as sort"
            (Error ["module 'MODULE'"] "Duplicated name: 's'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectAliasSentence (AliasName "s") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Definition with meta alias with same name as symbol"
            (Error ["module 'MODULE'"] "Duplicated name: '#a'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#a") stringSortName
                , simpleMetaSymbolSentence (SymbolName "#a") stringSortName
                ]
            )
        , expectFailureWithError
            "Definition with object alias with same name as symbol"
            (Error ["module 'MODULE'"] "Duplicated name: 'a'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectAliasSentence (AliasName "a") (SortName "s")
                , simpleObjectSymbolSentence (SymbolName "a") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
       , expectFailureWithError
            "Definition with meta symbol with same name as sort"
            (Error ["module 'MODULE'"] "Duplicated name: '#String'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaSymbolSentence
                    (SymbolName "#String") stringSortName
                ]
            )
        , expectFailureWithError
            "Definition with object symbol with same name as sort"
            (Error ["module 'MODULE'"] "Duplicated name: 's'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleObjectSymbolSentence (SymbolName "s") (SortName "s")
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Definition with an implicit meta symbol name"
            (Error ["module 'MODULE'"] "Duplicated name: '#nilCharList'.")
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ simpleMetaAliasSentence (AliasName "#nilCharList") stringSortName
                ]
            )
    ]
  where
    stringSortName = SortName (show (MetaListSortType CharSort))

