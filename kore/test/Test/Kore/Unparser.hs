module Test.Kore.Unparser
    ( test_parse
    , test_unparse
    , test_unparseGeneric
    ) where

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

import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Parser.Lexeme
import Kore.Parser.Parser
import Kore.Parser.ParserUtils
import Kore.Predicate.Predicate
    ( makeCeilPredicate
    , makeMultipleAndPredicate
    )
import Kore.Syntax
import Kore.Syntax.Definition
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable

import Test.Kore hiding
    ( Gen
    )
import qualified Test.Kore.Step.MockSymbols as Mock
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
                            asParsedPattern $ VariableF $ Const $ ElemVar
                            $ ElementVariable Variable
                                { variableName = testId "T"
                                , variableSort = SortVariableSort SortVariable
                                    { getSortVariable = testId "C" }
                                , variableCounter = mempty
                                }
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
        , unparseTest
            (makeMultipleAndPredicate @Variable
                [ makeCeilPredicate Mock.a
                , makeCeilPredicate Mock.b
                , makeCeilPredicate Mock.c
                ]
            )
            "\\and{_PREDICATE{}}(\n\
            \    \\ceil{testSort{}, _PREDICATE{}}(a{}()),\n\
            \\\and{_PREDICATE{}}(\n\
            \    \\ceil{testSort{}, _PREDICATE{}}(b{}()),\n\
            \    \\ceil{testSort{}, _PREDICATE{}}(c{}())\n\
            \))"
        , unparseTest
            (Pattern.andCondition
                (Pattern.topOf Mock.topSort)
                (Predicate.fromSubstitution $ Substitution.wrap
                    [ (ElemVar Mock.x, Mock.a)
                    , (ElemVar Mock.y, Mock.b)
                    , (ElemVar Mock.z, Mock.c)
                    ]
                )
            )
            "\\and{topSort{}}(\n\
            \    /* term: */\n\
            \    \\top{topSort{}}(),\n\
            \\\and{topSort{}}(\n\
            \    /* predicate: */\n\
            \    \\top{topSort{}}(),\n\
            \    /* substitution: */\n\
            \    \\and{topSort{}}(\n\
            \        \\equals{testSort{}, topSort{}}(x:testSort{}, a{}()),\n\
            \    \\and{topSort{}}(\n\
            \        \\equals{testSort{}, topSort{}}(y:testSort{}, b{}()),\n\
            \        \\equals{testSort{}, topSort{}}(z:testSort{}, c{}())\n\
            \    ))\n\
            \))"
        , unparseTest
            (Pattern.andCondition
                (Pattern.topOf Mock.topSort)
                (Predicate.andCondition
                    (Predicate.fromPredicate $ makeMultipleAndPredicate
                        [ makeCeilPredicate Mock.a
                        , makeCeilPredicate Mock.b
                        , makeCeilPredicate Mock.c
                        ]
                    )
                    (Predicate.fromSubstitution $ Substitution.wrap
                        [ (ElemVar Mock.x, Mock.a)
                        , (ElemVar Mock.y, Mock.b)
                        , (ElemVar Mock.z, Mock.c)
                        ]
                    )
                )
            )
            "\\and{topSort{}}(\n\
            \    /* term: */\n\
            \    \\top{topSort{}}(),\n\
            \\\and{topSort{}}(\n\
            \    /* predicate: */\n\
            \    \\and{topSort{}}(\n\
            \        \\ceil{testSort{}, topSort{}}(a{}()),\n\
            \    \\and{topSort{}}(\n\
            \        \\ceil{testSort{}, topSort{}}(b{}()),\n\
            \        \\ceil{testSort{}, topSort{}}(c{}())\n\
            \    )),\n\
            \    /* substitution: */\n\
            \    \\and{topSort{}}(\n\
            \        \\equals{testSort{}, topSort{}}(x:testSort{}, a{}()),\n\
            \    \\and{topSort{}}(\n\
            \        \\equals{testSort{}, topSort{}}(y:testSort{}, b{}()),\n\
            \        \\equals{testSort{}, topSort{}}(z:testSort{}, c{}())\n\
            \    ))\n\
            \))"
        ]

test_parse :: TestTree
test_parse =
    testGroup
        "Parse"
        [ testProperty "Generic testId" $ roundtrip idGen idParser
        , testProperty "StringLiteral" $
            roundtrip stringLiteralGen stringLiteralParser
        , testProperty "Object Symbol" $
            roundtrip symbolGen symbolParser
        , testProperty "Object Alias" $
            roundtrip aliasGen aliasParser
        , testProperty "Object SortVariable" $
            roundtrip sortVariableGen sortVariableParser
        , testProperty "Object Sort" $
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

roundtrip :: (Unparse a, Eq a, Show a) => Gen a -> Parser a -> Property
roundtrip generator parser =
    Hedgehog.property $ do
        generated <- Hedgehog.forAll generator
        parse parser (unparseToString generated) === Right generated

unparseParseTest
    :: (Unparse a, Debug a, Diff a) => Parser a -> a -> TestTree
unparseParseTest parser astInput =
    testCase
        "Parsing + unparsing."
        (assertEqual ""
            (Right astInput)
            (parse parser (unparseToString astInput)))

unparseTest :: (Unparse a, Debug a) => a -> String -> TestTree
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
data S = SA A | SB B | SC C deriving GHC.Generic

instance SOP.Generic S

-- A product type with three different symbols
data P = P A B C deriving GHC.Generic

instance SOP.Generic P

-- A complex algebraic type with sums and products
data D = D0 | D1 A | D2 A B | D3 A B C deriving GHC.Generic

instance SOP.Generic D

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
