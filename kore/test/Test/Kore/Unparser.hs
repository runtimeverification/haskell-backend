module Test.Kore.Unparser (
    test_parse,
    test_unparse,
    test_unparseGeneric,
) where

import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Hedgehog (
    Gen,
    Property,
    (===),
 )
import qualified Hedgehog
import Kore.Parser.Parser
import Kore.Parser.ParserUtils
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Unparser
import Prelude.Kore
import Test.Kore hiding (
    Gen,
 )
import Test.Kore.Parser (
    parse',
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Tasty.Hedgehog
import qualified Test.Terse as Terse

test_unparse :: TestTree
test_unparse =
    testGroup
        "Unparse"
        [ unparseTest
            ( asSentence
                ( SentenceSort
                    { sentenceSortName = testId "x"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    }
                ) ::
                ParsedSentence
            )
            "sort x{} []"
        , unparseTest
            Attributes
                { getAttributes =
                    [ embedParsedPattern
                        ( TopF
                            Top
                                { topSort =
                                    SortVariableSort
                                        SortVariable
                                            { getSortVariable = testId "#Fm"
                                            }
                                }
                        )
                    , embedParsedPattern
                        ( InF
                            In
                                { inOperandSort =
                                    SortActualSort
                                        SortActual
                                            { sortActualName = testId "B"
                                            , sortActualSorts = []
                                            }
                                , inResultSort =
                                    SortActualSort
                                        SortActual
                                            { sortActualName = testId "G"
                                            , sortActualSorts = []
                                            }
                                , inContainedChild =
                                    embedParsedPattern $
                                        VariableF $
                                            Const $
                                                inject $
                                                    mkElementVariable
                                                        (testId "T")
                                                        ( SortVariableSort
                                                            SortVariable
                                                                { getSortVariable = testId "C"
                                                                }
                                                        )
                                , inContainingChild =
                                    embedParsedPattern $
                                        StringLiteralF $
                                            Const
                                                StringLiteral{getStringLiteral = ""}
                                }
                        )
                    ]
                }
            "[\\top{#Fm}(), \\in{B{}, G{}}(T:C, \"\")]"
        , unparseTest
            ( Module
                { moduleName = ModuleName "t"
                , moduleSentences = []
                , moduleAttributes = Attributes []
                } ::
                ParsedModule
            )
            "module t\n\
            \endmodule\n\
            \[]"
        , unparseParseTest
            parseDefinition
            Definition
                { definitionAttributes = Attributes{getAttributes = []}
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName{getModuleName = "i"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes{getAttributes = []}
                        }
                    , Module
                        { moduleName = ModuleName{getModuleName = "k"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes{getAttributes = []}
                        }
                    ]
                }
        , unparseTest
            ( Definition
                { definitionAttributes = Attributes{getAttributes = []}
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName{getModuleName = "i"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes{getAttributes = []}
                        }
                    , Module
                        { moduleName = ModuleName{getModuleName = "k"}
                        , moduleSentences = []
                        , moduleAttributes = Attributes{getAttributes = []}
                        }
                    ]
                } ::
                ParsedDefinition
            )
            "[]\n\
            \module i\n\
            \endmodule\n\
            \[]\n\
            \module k\n\
            \endmodule\n\
            \[]"
        , unparseTest
            ( SentenceImportSentence
                SentenceImport
                    { sentenceImportModuleName = ModuleName{getModuleName = "sl"}
                    , sentenceImportAttributes =
                        Attributes{getAttributes = []} :: Attributes
                    } ::
                ParsedSentence
            )
            "import sl []"
        , unparseTest
            ( Attributes
                { getAttributes =
                    [ embedParsedPattern
                        ( TopF
                            Top
                                { topSort =
                                    SortActualSort
                                        SortActual
                                            { sortActualName = testId "#CharList"
                                            , sortActualSorts = []
                                            }
                                }
                        )
                    ]
                } ::
                Attributes
            )
            "[\\top{#CharList{}}()]"
        ]

test_parse :: TestTree
test_parse =
    testGroup
        "Parse"
        [ testProperty "Generic testId" $ roundtrip idGen parseId
        , testProperty "StringLiteral" $
            roundtrip stringLiteralGen parseStringLiteral
        , testProperty "ElementVariable" $ do
            let gen = standaloneGen (elementVariableGen =<< sortGen)
            roundtrip gen parseElementVariable
        , testProperty "SetVariable" $ do
            let gen = standaloneGen (setVariableGen =<< sortGen)
            roundtrip gen parseSetVariable
        , testProperty "Symbol" $
            roundtrip symbolGen parseSymbolHead
        , testProperty "Alias" $
            roundtrip aliasGen parseAliasHead
        , testProperty "SortVariable" $
            roundtrip sortVariableGen parseSortVariable
        , testProperty "Sort" $
            roundtrip (standaloneGen sortGen) parseSort
        , testProperty "ParsedPattern" $ roundtrip korePatternGen parsePattern
        , testProperty "Attributes" $
            roundtrip (standaloneGen attributesGen) parseAttributes
        , testProperty "Sentence" $
            roundtrip (standaloneGen koreSentenceGen) parseSentence
        , testProperty "Module" $
            roundtrip
                (standaloneGen $ moduleGen koreSentenceGen)
                parseModule
        , testProperty "Definition" $
            roundtrip
                (standaloneGen $ definitionGen koreSentenceGen)
                parseDefinition
        ]

roundtrip ::
    (HasCallStack, Unparse a, Eq a, Show a) => Gen a -> (FilePath -> Text -> Either String a) -> Property
roundtrip generator parser =
    Hedgehog.property $ do
        generated <- Hedgehog.forAll generator
        parse' (Parser parser) (unparseToText generated) === Right generated

unparseParseTest ::
    (HasCallStack, Unparse a, Debug a, Diff a) => (FilePath -> Text -> Either String a) -> a -> TestTree
unparseParseTest parser astInput =
    testCase
        "Parsing + unparsing."
        ( assertEqual
            ""
            (Right astInput)
            (parse' (Parser parser) (unparseToText astInput))
        )

unparseTest :: (HasCallStack, Unparse a, Debug a) => a -> String -> TestTree
unparseTest astInput expected =
    testCase
        "Unparsing"
        ( assertEqual
            (show $ debug astInput)
            expected
            (unparseToString astInput)
        )

-- -----------------------------------------------------------------------------
-- Generic unparsing tests

-- Three simple symbols
data A = A deriving stock (GHC.Generic)
data B = B deriving stock (GHC.Generic)
data C = C deriving stock (GHC.Generic)

instance Unparse A where
    unparse A = "A"
    unparse2 A = "A"

instance Unparse B where
    unparse B = "B"
    unparse2 B = "B"

instance Unparse C where
    unparse C = "C"
    unparse2 C = "C"

-- A sum type with three different symbols
data S = SA A | SB B | SC C
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic)

-- A product type with three different symbols
data P = P A B C
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic)

-- A complex algebraic type with sums and products
data D = D0 | D1 A | D2 A B | D3 A B C
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic)

test_unparseGeneric :: [TestTree]
test_unparseGeneric =
    [ SA A `yields` "A"
    , SB B `yields` "B"
    , SC C `yields` "C"
    , P A B C `yields` "A B C"
    , D0 `yields` ""
    , D1 A `yields` "A"
    , D2 A B `yields` "A B"
    , D3 A B C `yields` "A B C"
    ]
  where
    yields input = Terse.equals_ (show $ unparseGeneric input)
