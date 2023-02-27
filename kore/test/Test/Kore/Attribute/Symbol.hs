module Test.Kore.Attribute.Symbol (
    test_stepperAttributes,
    test_Anywhere,
    test_Memo,
    test_Klabel,
    test_SymbolKywd,
    test_NoEvaluators,
) where

import Data.Generics.Product
import Kore.Attribute.Hook
import Kore.Attribute.Parser
import Kore.Attribute.Symbol
import Kore.Error (
    Error,
 )
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Tasty (
    TestTree,
 )
import Test.Tasty.HUnit (
    Assertion,
    assertEqual,
    assertFailure,
    testCase,
 )

parse ::
    [AttributePattern] ->
    Either (Error ParseError) StepperAttributes
parse = parseAttributes . Attributes

testAttribute :: AttributePattern
testAttribute =
    (asAttributePattern . ApplicationF)
        Application
            { applicationSymbolOrAlias =
                SymbolOrAlias
                    { symbolOrAliasConstructor = "test" :: Id
                    , symbolOrAliasParams = []
                    }
            , applicationChildren = []
            }

badHookAttribute :: AttributePattern
badHookAttribute =
    (asAttributePattern . ApplicationF)
        Application
            { applicationSymbolOrAlias = hookSymbol :: SymbolOrAlias
            , applicationChildren = []
            }

expectError ::
    Show a =>
    String ->
    Either (Error ParseError) a ->
    Assertion
expectError _ (Left _) = pure ()
expectError what (Right got) =
    assertFailure
        ( "expected error parsing '" ++ what
            ++ "', but got: '"
            ++ show got
            ++ "'"
        )

test_stepperAttributes :: [TestTree]
test_stepperAttributes =
    [ testCase
        "Parsing a constructor attribute"
        ( assertEqual
            "[constructor{}()]"
            (Right Constructor{isConstructor = True})
            (constructor <$> parse [constructorAttribute])
        )
    , testCase
        "Parsing a function attribute"
        ( assertEqual
            "[function{}()]"
            (Right Function{isDeclaredFunction = True})
            (function <$> parse [functionAttribute])
        )
    , testCase
        "Parsing a total attribute"
        ( assertEqual
            "[total{}()]"
            (Right Total{isDeclaredTotal = True})
            (total <$> parse [totalAttribute])
        )
    , testCase
        "Parsing a hook attribute"
        ( assertEqual
            "[function{}(),hook{}(\"builtin\")]"
            (Right Hook{getHook = Just "builtin"})
            (hook <$> parse [hookAttribute "builtin"])
        )
    , testCase
        "Parsing an illegal hook attribute"
        ( expectError
            "[hook{}()]"
            (parse [badHookAttribute])
        )
    , testCase
        "Parsing repeated hook attribute"
        ( expectError
            "[function{}(),hook{}(\"BUILTIN.1\"),hook{}(\"BUILTIN.2\")]"
            (parse [badHookAttribute])
        )
    , testCase
        "Ignoring unknown attribute"
        ( assertEqual
            "[test{}()]"
            (Right def)
            (parse [testAttribute])
        )
    , testCase
        "Testing parseAttributes"
        ( assertEqual
            "[total{}(),function{}(),hook{}(\"builtin\")]"
            ( defaultSymbolAttributes
                & setTyped (Function True)
                & setTyped (Total True)
                & setTyped (Hook $ Just "builtin")
                & Right
            )
            ( parse
                [ functionAttribute
                , totalAttribute
                , testAttribute
                , hookAttribute "builtin"
                ]
            )
        )
    ]

test_Anywhere :: [TestTree]
test_Anywhere =
    [ testCase "parseAttribute" $
        assertEqual
            "[anywhere{}()]"
            (Right Anywhere{isAnywhere = True})
            (anywhere <$> parse [anywhereAttribute])
    , testCase "defaultSymbolAttributes" $
        assertEqual
            "[]"
            (Right def)
            (anywhere <$> parse [])
    , testCase "isInjective" $
        assertEqual
            ""
            (Right False)
            (isInjective <$> parse [anywhereAttribute])
    ]

test_Memo :: [TestTree]
test_Memo =
    [ testCase "parseAttribute" $
        assertEqual
            "[memo{}()]"
            (Right Memo{isMemo = True})
            (memo <$> parse [memoAttribute])
    , testCase "defaultSymbolAttributes" $
        assertEqual
            "[]"
            (Right def)
            (memo <$> parse [])
    ]

test_Klabel :: [TestTree]
test_Klabel =
    [ testCase "parseAttribute" $
        assertEqual
            "[klabel{}(\"string\")]"
            (Right Klabel{getKlabel = Just "string"})
            (klabel <$> parse [klabelAttribute "string"])
    , testCase "defaultSymbolAttributes" $
        assertEqual
            "[]"
            (Right def)
            (klabel <$> parse [])
    ]

test_SymbolKywd :: [TestTree]
test_SymbolKywd =
    [ testCase "parseAttribute" $
        assertEqual
            "[symbolKywd{}()]"
            (Right SymbolKywd{isSymbolKywd = True})
            (symbolKywd <$> parse [symbolKywdAttribute])
    , testCase "defaultSymbolAttributes" $
        assertEqual
            "[]"
            (Right def)
            (symbolKywd <$> parse [])
    ]

test_NoEvaluators :: [TestTree]
test_NoEvaluators =
    [ testCase "parseAttribute" $
        assertEqual
            "[noEvaluators{}[]]"
            (Right NoEvaluators{hasNoEvaluators = True})
            (noEvaluators <$> parse [noEvaluatorsAttribute])
    , testCase "defaultSymbolAttributes" $
        assertEqual
            "[]"
            (Right def)
            (noEvaluators <$> parse [])
    ]
