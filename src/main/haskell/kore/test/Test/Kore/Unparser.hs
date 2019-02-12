module Test.Kore.Unparser
    ( test_parse
    , test_unparse
    ) where

import           Hedgehog
                 ( Gen, Property, (===) )
import qualified Hedgehog
import           Test.Tasty
                 ( TestTree, testGroup )
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit
                 ( assertEqual, testCase )

import Kore.AST.Kore
import Kore.AST.Sentence
import Kore.Parser.Lexeme
import Kore.Parser.ParserImpl
import Kore.Parser.ParserUtils
import Kore.Unparser

import Test.Kore

test_unparse :: TestTree
test_unparse =
    testGroup
        "Unparse"
        [ unparseTest
            (asSentence
                (SentenceSort
                    { sentenceSortName = testId "x"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    }
                    :: KoreSentenceSort Object
                )
            )
            "sort x{} []"
        , unparseTest
            Attributes
                { getAttributes =
                    [ asCommonKorePattern (TopPattern Top
                        { topSort = SortVariableSort SortVariable
                            { getSortVariable = testId "#Fm" :: Id Meta }
                        })
                    , asCommonKorePattern (InPattern In
                        { inOperandSort = SortActualSort SortActual
                            { sortActualName = testId "B" :: Id Object
                            , sortActualSorts = []
                            }
                        , inResultSort = SortActualSort SortActual
                            { sortActualName = testId "G" :: Id Object
                            , sortActualSorts = []
                            }
                        , inContainedChild =
                            asCommonKorePattern $ VariablePattern Variable
                                { variableName = testId "T" :: Id Object
                                , variableSort = SortVariableSort SortVariable
                                    { getSortVariable = testId "C" }
                                , variableCounter = mempty
                                }
                        , inContainingChild = asCommonKorePattern (StringLiteralPattern
                            StringLiteral { getStringLiteral = "" })
                        })
                    ]
                }
            "[\\top{#Fm}(), \\in{B{}, G{}}(T:C, \"\")]"
        , unparseTest
            (Module
                { moduleName = ModuleName "t"
                , moduleSentences = []
                , moduleAttributes = Attributes []
                }
                :: KoreModule
            )
            "module t\n\
            \endmodule\n\
            \[]"
        , unparseParseTest
            koreDefinitionParser
            Definition
                { definitionAttributes = Attributes {getAttributes = []}
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName {getModuleName = "i"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes {getAttributes = []}
                        }
                    , Module
                        { moduleName = ModuleName {getModuleName = "k"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes {getAttributes = []}
                        }
                    ]
                }
        , unparseTest
            (Definition
                { definitionAttributes = Attributes {getAttributes = []}
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName {getModuleName = "i"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes {getAttributes = []}
                        }
                    , Module
                        { moduleName = ModuleName {getModuleName = "k"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes {getAttributes = []}
                        }
                    ]
                }
                :: KoreDefinition
            )
            "[]\n\
            \module i\n\
            \endmodule\n\
            \[]\n\
            \module k\n\
            \endmodule\n\
            \[]"
        , unparseTest
            ( constructUnifiedSentence SentenceImportSentence $ SentenceImport
                { sentenceImportModuleName = ModuleName {getModuleName = "sl"}
                , sentenceImportAttributes =
                    Attributes { getAttributes = [] } :: Attributes
                }
                :: KoreSentence
            )
            "import sl []"
        , unparseTest
            (Attributes
                { getAttributes =
                    [ asCommonKorePattern
                        ( TopPattern Top
                            { topSort = SortActualSort SortActual
                                { sortActualName = testId "#CharList" :: Id Meta
                                , sortActualSorts = []
                                }
                            }
                        )
                    ]
                }::Attributes
            )
            "[\\top{#CharList{}}()]"
        , unparseTest
            (Attributes
                { getAttributes =
                    [ asCommonKorePattern
                        (CharLiteralPattern CharLiteral
                            { getCharLiteral = '\'' }
                        )
                    , asCommonKorePattern
                        (CharLiteralPattern CharLiteral
                            { getCharLiteral = '\'' }
                        )
                    ]
                }::Attributes
            )
            "[''', ''']"
        ]

test_parse :: TestTree
test_parse =
    testGroup
        "Parse"
        [ testProperty "Object testId" $
            roundtrip (idGen IsObject) (idParser Object)
        , testProperty "Meta testId" $
            roundtrip (idGen IsMeta) (idParser Meta)
        , testProperty "StringLiteral" $
            roundtrip stringLiteralGen stringLiteralParser
        , testProperty "CharLiteral" $
            roundtrip charLiteralGen charLiteralParser
        , testProperty "Object Symbol" $
            roundtrip symbolGen (symbolParser Object)
        , testProperty "Meta Symbol" $
            roundtrip symbolGen (symbolParser Meta)
        , testProperty "Object Alias" $
            roundtrip aliasGen (aliasParser Object)
        , testProperty "Meta Alias" $
            roundtrip aliasGen (aliasParser Meta)
        , testProperty "Object SortVariable" $
            roundtrip sortVariableGen (sortVariableParser Object)
        , testProperty "Meta SortVariable" $
            roundtrip sortVariableGen (sortVariableParser Meta)
        , testProperty "Object Sort" $
            roundtrip (standaloneGen sortGen) (sortParser Object)
        , testProperty "Meta Sort" $
            roundtrip (standaloneGen sortGen) (sortParser Meta)
        , testProperty "UnifiedVariable" $
            roundtrip
                (standaloneGen $ unifiedVariableGen =<< unifiedSortGen)
                unifiedVariableParser
        , testProperty "CommonKorePattern" $
            roundtrip korePatternGen korePatternParser
        , testProperty "Attributes" $
            roundtrip (standaloneGen attributesGen) attributesParser
        , testProperty "Sentence" $
            roundtrip (standaloneGen koreSentenceGen) koreSentenceParser
        , testProperty "Module" $
            roundtrip
                (standaloneGen $ moduleGen koreSentenceGen)
                (moduleParser koreSentenceParser)
        , testProperty "Definition" $
            roundtrip
                (standaloneGen $ definitionGen koreSentenceGen)
                (definitionParser koreSentenceParser)
        ]

parse :: Parser a -> String -> Either String a
parse parser =
    parseOnly (parser <* endOfInput) "<test-string>"

roundtrip :: (Unparse a, Eq a, Show a) => Gen a -> Parser a -> Property
roundtrip generator parser =
    Hedgehog.property $ do
        generated <- Hedgehog.forAll generator
        parse parser (unparseToString generated) === Right generated

unparseParseTest
    :: (Unparse a, Eq a, Show a) => Parser a -> a -> TestTree
unparseParseTest parser astInput =
    testCase
        "Parsing + unparsing."
        (assertEqual ""
            (Right astInput)
            (parse parser (unparseToString astInput)))

unparseTest :: (Unparse a, Show a) => a -> String -> TestTree
unparseTest astInput expected =
    testCase
        "Unparsing"
        (assertEqual (show astInput)
            expected
            (unparseToString astInput))
