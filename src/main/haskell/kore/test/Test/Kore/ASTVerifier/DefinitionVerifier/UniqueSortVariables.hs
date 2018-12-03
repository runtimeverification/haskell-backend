module Test.Kore.ASTVerifier.DefinitionVerifier.UniqueSortVariables
    ( test_uniqueSortVariables
    ) where

import Test.Tasty
       ( TestTree )

import Kore.AST.MetaOrObject
import Kore.AST.PureToKore
import Kore.AST.Sentence
import Kore.ASTUtils.SmartPatterns
import Kore.Error
import Kore.Implicit.ImplicitSorts
import Kore.Sort

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
                [ sortVariable @Object "sv1" ]
            ]
        )
    , expectSuccess "Sort with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters
                (SortName "s")
                [ sortVariable @Object "s" ]
            ]
        )
    , expectSuccess "Sort with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ sortSentenceWithSortParameters
                (SortName "s")
                [ sortVariable @Object "sv1"
                , sortVariable @Object "sv2"
                ]
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with meta alias"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a") charListMetaSort []
            ]
        )
    , expectSuccess "Meta alias with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                charListMetaSort
                [ sortVariable @Meta "#sv" ]
            ]
        )
    , expectSuccess "Meta alias with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                charListMetaSort
                [ sortVariable @Meta "#a" ]
            ]
        )
    , expectSuccess
        "Meta alias with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                charListMetaSort
                [ sortVariable @Meta "#String" ]
            ]
        )
    , expectSuccess
        "Meta alias with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaAliasSentenceWithSortParameters
                (AliasName "#a")
                charListMetaSort
                [ sortVariable @Meta "#sv1"
                , sortVariable @Meta "#sv2"
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
                    (patternPureToKore
                        $ Top_ (simpleSort (SortName "s") :: Sort Object))
                :: KoreSentenceAlias Object
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
                    [ sortVariable @Object "sv" ]
                    (patternPureToKore
                        $ Top_ (simpleSort (SortName "s") :: Sort Object))
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
                    [ sortVariable @Object "a" ]
                    (patternPureToKore
                        $ Top_ (simpleSort (SortName "s") :: Sort Object))
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
                    [ sortVariable @Object "s" ]
                    (patternPureToKore
                        $ Top_ (simpleSort (SortName "s") :: Sort Object))
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
                    [ sortVariable @Object "sv1"
                    , sortVariable @Object "sv2"
                    ]
                    (patternPureToKore
                        $ Top_ (simpleSort (SortName "s") :: Sort Object))
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with meta symbol"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaSymbolSentenceWithSortParameters
                (SymbolName "#a") charListMetaSort []
            ]
        )
    , expectSuccess "Meta symbol with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaSymbolSentenceWithSortParameters
                (SymbolName "#a")
                charListMetaSort
                [ sortVariable @Meta "#sv" ]
            ]
        )
    , expectSuccess "Meta symbol with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaSymbolSentenceWithSortParameters
                (SymbolName "#a")
                charListMetaSort
                [ sortVariable @Meta "#a" ]
            ]
        )
    , expectSuccess
        "Meta symbol with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaSymbolSentenceWithSortParameters
                (SymbolName "#a")
                charListMetaSort
                [ sortVariable @Meta "#String" ]
            ]
        )
    , expectSuccess
        "Meta symbol with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ metaSymbolSentenceWithSortParameters
                (SymbolName "#a")
                charListMetaSort
                [ sortVariable @Meta "#sv1"
                , sortVariable @Meta "#sv2"
                ]
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with object symbol"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (symbolSentenceWithSortParameters
                    (SymbolName "a") (SortName "s") []
                :: KoreSentenceSymbol Object
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object symbol with one sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (symbolSentenceWithSortParameters
                    (SymbolName "a")
                    (SortName "s")
                    [ sortVariable @Object "sv" ]
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object symbol with one sort parameter with same name"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (symbolSentenceWithSortParameters
                    (SymbolName "a")
                    (SortName "s")
                    [ sortVariable @Object  "a" ]
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess
        "Object symbol with one sort parameter with same name as sort"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (symbolSentenceWithSortParameters
                    (SymbolName "a")
                    (SortName "s")
                    [ sortVariable @Object "s" ]
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    , expectSuccess "Object symbol with two sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ asSentence
                (symbolSentenceWithSortParameters
                    (SymbolName "a")
                    (SortName "s")
                    [ sortVariable @Object  "sv1"
                    , sortVariable @Object  "sv2"
                    ]
                )
            , simpleSortSentence (SortName "s")
            ]
        )
    ------------------------------------------------------------------
    , expectSuccess "Definition with axiom"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringUnifiedPattern "hello") []
            ]
        )
    , expectSuccess "Axiom with one object sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Object (SortVariableName "sv") ]
            ]
        )
    , expectSuccess "Axiom with one meta sort parameter"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Meta (SortVariableName "#sv") ]
            ]
        )
    , expectSuccess "Axiom with two object sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Object (SortVariableName "sv1")
                , unifiedSortVariable Object (SortVariableName "sv2")
                ]
            ]
        )
    , expectSuccess "Axiom with two meta sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Meta (SortVariableName "#sv1")
                , unifiedSortVariable Meta (SortVariableName "#sv2")
                ]
            ]
        )
    , expectSuccess "Axiom with mixed sort parameters"
        ( simpleDefinitionFromSentences (ModuleName "MODULE")
            [ axiomSentenceWithSortParameters
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Object (SortVariableName "sv")
                , unifiedSortVariable Meta (SortVariableName "#sv")
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
                [ sortVariable @Object "sv"
                , sortVariable @Object "sv"
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
                charListMetaSort
                [ sortVariable @Meta "#sv"
                , sortVariable @Meta "#sv"
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
                    [ sortVariable @Object "sv"
                    , sortVariable @Object "sv"
                    ]
                    (patternPureToKore
                        $ Top_ (simpleSort (SortName "s1") :: Sort Object))
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
            [ metaSymbolSentenceWithSortParameters
                (SymbolName "#a")
                charListMetaSort
                [ sortVariable @Meta "#sv"
                , sortVariable @Meta "#sv"
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
            [ asSentence
                (symbolSentenceWithSortParameters
                    (SymbolName "a")
                    (SortName "s")
                    [ sortVariable @Object "sv"
                    , sortVariable @Object "sv"
                    ]
                )
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
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Object (SortVariableName "sv")
                , unifiedSortVariable Object (SortVariableName "sv")
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
                (stringUnifiedPattern "hello")
                [ unifiedSortVariable Meta (SortVariableName "#sv")
                , unifiedSortVariable Meta (SortVariableName "#sv")
                ]
            ]
        )
    ]
