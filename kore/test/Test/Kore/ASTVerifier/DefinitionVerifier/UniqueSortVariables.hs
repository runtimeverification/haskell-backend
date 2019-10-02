module Test.Kore.ASTVerifier.DefinitionVerifier.UniqueSortVariables
    ( test_uniqueSortVariables
    ) where

import Test.Tasty
    ( TestTree
    )

import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.Internal.TermLike
import Kore.Syntax.Definition
    ( ModuleName (..)
    , asSentence
    )

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

test_uniqueSortVariables :: [TestTree]
test_uniqueSortVariables =
    [ expectSuccess "Simplest definition"
        (simpleDefinitionFromSentences (ModuleName "MODULE") [])
    , expectSuccess "Definition with sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters (SortName "s") [] ]
        )
    , expectSuccess "Sort with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters
                (SortName "s")
                [ sortVariable "sv1" ]
            ]
        )
    , expectSuccess "Sort with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters
                (SortName "s")
                [ sortVariable "s" ]
            ]
        )
    , expectSuccess "Sort with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters
                (SortName "s")
                [ sortVariable "sv1"
                , sortVariable "sv2"
                ]
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with meta alias"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a") stringMetaSort []
            ]
        )
    , expectSuccess "Meta alias with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                stringMetaSort
                [ sortVariable "#sv" ]
            ]
        )
    , expectSuccess "Meta alias with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                stringMetaSort
                [ sortVariable "#a" ]
            ]
        )
    , expectSuccess
        "Meta alias with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                stringMetaSort
                [ sortVariable "#String" ]
            ]
        )
    , expectSuccess
        "Meta alias with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                stringMetaSort
                [ sortVariable "#sv1"
                , sortVariable "#sv2"
                ]
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with object alias"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (aliasSentenceWithSortParameters
                    (AliasName "a")
                    (SortName "s")
                    []
                    topS
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object alias with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (aliasSentenceWithSortParameters
                    (AliasName "a")
                    (SortName "s")
                    [ sortVariable "sv" ]
                    topS
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object alias with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (aliasSentenceWithSortParameters
                    (AliasName "a")
                    (SortName "s")
                    [ sortVariable "a" ]
                    topS
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess
        "Object alias with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (aliasSentenceWithSortParameters
                    (AliasName "a")
                    (SortName "s")
                    [ sortVariable "s" ]
                    topS
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object alias with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (aliasSentenceWithSortParameters
                    (AliasName "a")
                    (SortName "s")
                    [ sortVariable "sv1"
                    , sortVariable "sv2"
                    ]
                    topS
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with meta symbol"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "#a") stringMetaSort []
            ]
        )
    , expectSuccess "Meta symbol with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "#a")
                stringMetaSort
                [ sortVariable "#sv" ]
            ]
        )
    , expectSuccess "Meta symbol with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "#a")
                stringMetaSort
                [ sortVariable "#a" ]
            ]
        )
    , expectSuccess
        "Meta symbol with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "#a")
                stringMetaSort
                [ sortVariable "#String" ]
            ]
        )
    , expectSuccess
        "Meta symbol with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "#a")
                stringMetaSort
                [ sortVariable "#sv1"
                , sortVariable "#sv2"
                ]
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with object symbol"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "a")
                (simpleSort $ SortName "s")
                []
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object symbol with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "a")
                (simpleSort $ SortName "s")
                [ sortVariable "sv" ]
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object symbol with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "a")
                (simpleSort $ SortName "s")
                [ sortVariable  "a" ]
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess
        "Object symbol with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "a")
                (simpleSort $ SortName "s")
                [ sortVariable "s" ]
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object symbol with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "a")
                (simpleSort $ SortName "s")
                [ sortVariable  "sv1"
                , sortVariable  "sv2"
                ]
            , simpleSortSentence (SortName "s")
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with axiom"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello") []
            ]
        )
    , expectSuccess "Axiom with one object sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "sv") ]
            ]
        )
    , expectSuccess "Axiom with one meta sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "#sv") ]
            ]
        )
    , expectSuccess "Axiom with two object sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "sv1")
                , namedSortVariable (SortVariableName "sv2")
                ]
            ]
        )
    , expectSuccess "Axiom with two meta sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "#sv1")
                , namedSortVariable (SortVariableName "#sv2")
                ]
            ]
        )
    , expectSuccess "Axiom with mixed sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "sv")
                , namedSortVariable (SortVariableName "#sv")
                ]
            ]
        )
    ------------------------------------------------------------------
    , expectFailureWithError
        "Sort with two sort parameters with same name"
        (Error
            ["module 'MODULE'"
            , "sort 's' declaration (<test data>)"
            , "(<test data>)"
            ]
            "Duplicated sort variable: 'sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters
                (SortName "s")
                [ sortVariable "sv"
                , sortVariable "sv"
                ]
            ]
        )
    , expectFailureWithError
        "Meta alias with two sort parameters with same name"
        (Error
            [ "module 'MODULE'"
            , "alias '#a' declaration (<test data>)"
            , "(<test data>)"
            ]
            "Duplicated sort variable: '#sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                stringMetaSort
                [ sortVariable "#sv"
                , sortVariable "#sv"
                ]
            ]
        )
    , expectFailureWithError
        "Object alias with two sort parameters with same name"
        (Error
            [ "module 'MODULE'"
            , "alias 'a' declaration (<test data>)"
            , "(<test data>)"
            ]
            "Duplicated sort variable: 'sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (aliasSentenceWithSortParameters
                    (AliasName "a")
                    (SortName "s")
                    [ sortVariable "sv"
                    , sortVariable "sv"
                    ]
                    topS1
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectFailureWithError
        "Meta symbol with two sort parameters with same name"
        (Error
            [ "module 'MODULE'"
            , "symbol '#a' declaration (<test data>)"
            , "(<test data>)"
            ]
            "Duplicated sort variable: '#sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                (SymbolName "#a")
                stringMetaSort
                [ sortVariable "#sv"
                , sortVariable "#sv"
                ]
            ]
        )
    , expectFailureWithError
        "Object symbol with two sort parameters with same name"
        (Error
            [ "module 'MODULE'"
            , "symbol 'a' declaration (<test data>)"
            , "(<test data>)"
            ]
            "Duplicated sort variable: 'sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ symbolSentenceWithSortParameters
                    (SymbolName "a")
                    (simpleSort $ SortName "s")
                    [ sortVariable "sv"
                    , sortVariable "sv"
                    ]
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectFailureWithError
        "Axiom with two object sort parameters with same name"
        (Error
            ["module 'MODULE'", "axiom declaration", "(<test data>)"]
            "Duplicated sort variable: 'sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "sv")
                , namedSortVariable (SortVariableName "sv")
                ]
            ]
        )
    , expectFailureWithError
        "Axiom with two meta sort parameters with same name"
        (Error
            ["module 'MODULE'", "axiom declaration", "(<test data>)"]
            "Duplicated sort variable: '#sv'."
        )
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringParsedPattern "hello")
                [ namedSortVariable (SortVariableName "#sv")
                , namedSortVariable (SortVariableName "#sv")
                ]
            ]
        )
    ]
  where
    topS  = Builtin.externalize $ mkTop $ simpleSort $ SortName "s"
    topS1 = Builtin.externalize $ mkTop $ simpleSort $ SortName "s1"
