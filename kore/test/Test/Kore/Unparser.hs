module Test.Kore.Unparser
    ( test_parse
    , test_unparse
    , test_unparseGeneric
    ) where

import Prelude.Kore

import Hedgehog
    ( Gen
    , Property
    , (===)
    )
import qualified Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Parser.Lexeme
import Kore.Parser.Parser
import Kore.Parser.ParserUtils
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Unparser

import Test.Kore hiding
    ( Gen
    )
import Test.Tasty.HUnit.Ext
import qualified Test.Terse as Terse

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
                    :: ParsedSentenceSort
                )
            )
            "sort x{} []"
        , unparseTest
            Attributes
                { getAttributes =
                    [ asParsedPattern (TopF Top
                        { topSort = SortVariableSort SortVariable
                            { getSortVariable = testId "#Fm" }
                        })
                    , asParsedPattern (InF In
                        { inOperandSort = SortActualSort SortActual
                            { sortActualName = testId "B"
                            , sortActualSorts = []
                            }
                        , inResultSort = SortActualSort SortActual
                            { sortActualName = testId "G"
                            , sortActualSorts = []
                            }
                        , inContainedChild =
                            asParsedPattern $ VariableF $ Const $ inject
                            $ mkElementVariable
                                (testId "T")
                                (SortVariableSort SortVariable
                                    { getSortVariable = testId "C" }
                                )
                        , inContainingChild =
                            asParsedPattern
                            $ StringLiteralF $ Const
                                StringLiteral { getStringLiteral = "" }
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
                :: ParsedModule
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
                :: ParsedDefinition
            )
            "[]\n\
            \module i\n\
            \endmodule\n\
            \[]\n\
            \module k\n\
            \endmodule\n\
            \[]"
        , unparseTest
            ( SentenceImportSentence SentenceImport
                { sentenceImportModuleName = ModuleName {getModuleName = "sl"}
                , sentenceImportAttributes =
                    Attributes { getAttributes = [] } :: Attributes
                }
                :: ParsedSentence
            )
            "import sl []"
        , unparseTest
            (Attributes
                { getAttributes =
                    [ asParsedPattern
                        ( TopF Top
                            { topSort = SortActualSort SortActual
                                { sortActualName = testId "#CharList"
                                , sortActualSorts = []
                                }
                            }
                        )
                    ]
                }::Attributes
            )
            "[\\top{#CharList{}}()]"
        ]

test_parse :: TestTree
test_parse =
    testGroup "Parse"
        [ testProperty "Generic testId" $ roundtrip idGen idParser
        , testProperty "StringLiteral" $
            roundtrip stringLiteralGen stringLiteralParser
        , testProperty "ElementVariable" $ do
            let gen = standaloneGen (elementVariableGen =<< sortGen)
            roundtrip gen elementVariableParser
        , testProperty "SetVariable" $ do
            let gen = standaloneGen (setVariableGen =<< sortGen)
            roundtrip gen setVariableParser
        , testProperty "Symbol" $
            roundtrip symbolGen symbolParser
        , testProperty "Alias" $
            roundtrip aliasGen aliasParser
        , testProperty "SortVariable" $
            roundtrip sortVariableGen sortVariableParser
        , testProperty "Sort" $
            roundtrip (standaloneGen sortGen) sortParser
        , testProperty "ParsedPattern" $
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

roundtrip
    :: (HasCallStack, Unparse a, Eq a, Show a) => Gen a -> Parser a -> Property
roundtrip generator parser =
    Hedgehog.property $ do
        generated <- Hedgehog.forAll generator
        parse parser (unparseToString generated) === Right generated

unparseParseTest
    :: (HasCallStack, Unparse a, Debug a, Diff a) => Parser a -> a -> TestTree
unparseParseTest parser astInput =
    testCase
        "Parsing + unparsing."
        (assertEqual ""
            (Right astInput)
            (parse parser (unparseToString astInput)))

unparseTest :: (HasCallStack, Unparse a, Debug a) => a -> String -> TestTree
unparseTest astInput expected =
    testCase
        "Unparsing"
        (assertEqual (show $ debug astInput)
            expected
            (unparseToString astInput))

-- -----------------------------------------------------------------------------
-- Generic unparsing tests

-- Three simple symbols
data A = A deriving GHC.Generic
data B = B deriving GHC.Generic
data C = C deriving GHC.Generic

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
    deriving GHC.Generic
    deriving anyclass (SOP.Generic)

-- A product type with three different symbols
data P = P A B C
    deriving GHC.Generic
    deriving anyclass (SOP.Generic)

-- A complex algebraic type with sums and products
data D = D0 | D1 A | D2 A B | D3 A B C
    deriving GHC.Generic
    deriving anyclass (SOP.Generic)

test_unparseGeneric :: [TestTree]
test_unparseGeneric =
    [ SA A     `yields` "A"
    , SB B     `yields` "B"
    , SC C     `yields` "C"
    , P A B C  `yields` "A B C"
    , D0       `yields` ""
    , D1 A     `yields` "A"
    , D2 A B   `yields` "A B"
    , D3 A B C `yields` "A B C"
    ]
  where
    yields input = Terse.equals_ (show $ unparseGeneric input)
