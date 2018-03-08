module Data.Kore.Unparser.UnparseTest ( unparseParseTests
                                      , unparseUnitTests
                                      ) where

import           Data.Kore.AST
import           Data.Kore.ASTGen
import           Data.Kore.Parser.LexemeImpl
import           Data.Kore.Parser.ParserImpl
import           Data.Kore.Unparser.Unparse

import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertEqual, testCase)
import           Test.Tasty.QuickCheck            (forAll, testProperty)

unparseUnitTests :: TestTree
unparseUnitTests =
    testGroup
        "Unparse unit tests"
        [ unparseTest
            (SentenceSortSentence
                SentenceSort
                    { sentenceSortName = Id "x"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    })
            "sort x{}[]"
        , unparseTest
            Attributes
                { getAttributes =
                    [ MetaPattern (TopPattern Top
                        { topSort = SortVariableSort SortVariable
                            { getSortVariable = Id {getId = "#Fm"} }
                        })
                    , ObjectPattern (InPattern In
                        { inOperandSort = SortActualSort SortActual
                            { sortActualName = Id {getId = "B"}
                            , sortActualSorts = []
                            }
                        , inResultSort = SortActualSort SortActual
                            { sortActualName = Id {getId = "G"}
                            , sortActualSorts = []
                            }
                        , inContainedChild = ObjectPattern $ VariablePattern Variable
                            { variableName = Id {getId = "T"}
                            , variableSort = SortVariableSort SortVariable
                                { getSortVariable = Id {getId = "C"} }
                            }
                        , inContainingChild = MetaPattern (StringLiteralPattern
                            StringLiteral { getStringLiteral = "" })
                        })
                    ]
                }
            "[\n\
            \    \\top{#Fm}(),\n\
            \    \\in{\n\
            \        B{},\n\
            \        G{}\n\
            \    }(\n\
            \        T:C,\n\
            \        \"\"\n\
            \    )\n\
            \]"
        , unparseTest
            Module
                { moduleName = ModuleName "t"
                , moduleSentences = []
                , moduleAttributes = Attributes []
                }
            "module t\nendmodule\n[]"
        , unparseParseTest
            definitionParser
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
            (  "[]\n\n"
            ++ "    module i\n    endmodule\n    []\n"
            ++ "    module k\n    endmodule\n    []\n"
            )
        , unparseTest
            ( SentenceImportSentence SentenceImport
                { sentenceImportModuleName = ModuleName {getModuleName = "sl"}
                , sentenceImportAttributes = Attributes { getAttributes = [] }
                }
            )
            "import sl[]"
        , unparseTest
            Attributes
                { getAttributes =
                    [ MetaPattern
                        ( TopPattern Top
                            { topSort = SortActualSort SortActual
                                { sortActualName = Id { getId = "#CharList" }
                                , sortActualSorts = []
                                }
                            }
                        )
                    ]
                }
        "[\n    \\top{#CharList{}}()\n]"
        , unparseTest
            Attributes
                { getAttributes =
                    [ MetaPattern
                        (CharLiteralPattern CharLiteral
                            { getCharLiteral = '\'' }
                        )
                    , MetaPattern
                        (CharLiteralPattern CharLiteral
                            { getCharLiteral = '\'' }
                        )
                    ]
                }
            "[\n    '\\'',\n    '\\''\n]"
        ]

unparseParseTests :: TestTree
unparseParseTests =
    testGroup
        "QuickCheck Unparse&Parse Tests"
        [ testProperty "Object Id"
            (forAll (idGen Object) (unparseParseProp (idParser Object)))
        , testProperty "Meta Id"
            (forAll (idGen Meta) (unparseParseProp (idParser Meta)))
        , testProperty "StringLiteral"
            (forAll stringLiteralGen (unparseParseProp stringLiteralParser))
        , testProperty "CharLiteral"
            (forAll charLiteralGen (unparseParseProp charLiteralParser))
        , testProperty "Object Symbol"
            (forAll (symbolGen Object) (unparseParseProp (symbolParser Object)))
        , testProperty "Meta Symbol"
            (forAll (symbolGen Meta) (unparseParseProp (symbolParser Meta)))
        , testProperty "Object Alias"
            (forAll (aliasGen Object) (unparseParseProp (aliasParser Object)))
        , testProperty "Meta Alias"
            (forAll (aliasGen Meta) (unparseParseProp (aliasParser Meta)))
        , testProperty "Object SortVariable"
            (forAll (sortVariableGen Object)
                (unparseParseProp (sortVariableParser Object))
            )
        , testProperty "Meta SortVariable"
            (forAll (sortVariableGen Meta)
                (unparseParseProp (sortVariableParser Meta))
            )
        , testProperty "Object Sort"
            (forAll (sortGen Object)
                (unparseParseProp (sortParser Object))
            )
        , testProperty "Meta Sort"
            (forAll (sortGen Meta)
                (unparseParseProp (sortParser Meta))
            )
        , testProperty "UnifiedVariable"
            (forAll unifiedVariableGen (unparseParseProp unifiedVariableParser))
        , testProperty "UnifiedPattern"
            (forAll unifiedPatternGen (unparseParseProp patternParser))
        , testProperty "Attributes"
            (forAll attributesGen (unparseParseProp attributesParser))
        , testProperty "Sentence"
            (forAll sentenceGen (unparseParseProp sentenceParser))
        , testProperty "Module"
            (forAll moduleGen (unparseParseProp moduleParser))
        , testProperty "Definition"
            (forAll definitionGen (unparseParseProp definitionParser))
        ]

parse :: Parser.Parser a -> String -> Either String a
parse parser input =
    Parser.parseOnly (parser <* Parser.endOfInput) (Char8.pack input)

unparseParseProp :: (Unparse a, Eq a) => Parser.Parser a -> a -> Bool
unparseParseProp p a = parse p (unparseToString a) == Right a

unparseParseTest
    :: (Unparse a, Eq a, Show a) => Parser.Parser a -> a -> TestTree
unparseParseTest parser astInput =
    testCase
        "Parsing + unparsing."
        (assertEqual "Expecting unparse success!"
            (Right astInput)
            (parse parser (unparseToString astInput)))

unparseTest :: (Unparse a, Show a) => a -> String -> TestTree
unparseTest astInput expected =
    testCase
        "Unparsing"
        (assertEqual ("Expecting unparse success!" ++ show astInput)
            expected
            (unparseToString astInput))
