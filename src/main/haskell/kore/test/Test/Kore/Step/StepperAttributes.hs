module Test.Kore.Step.StepperAttributes (test_stepperAttributes) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( Assertion, assertEqual, assertFailure, testCase )

import qualified Control.Lens as Lens
import           Data.Default
                 ( def )
import           Data.Function
                 ( (&) )

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.Sentence
       ( Attributes (..) )
import Kore.Attribute.Hook
import Kore.Attribute.Parser
       ( ParseError, parseAttributes )
import Kore.Error
       ( Error )
import Kore.Step.StepperAttributes

import Test.Kore.Comparators ()

parse
    :: [CommonKorePattern]
    -> Either (Error ParseError) StepperAttributes
parse = parseAttributes . Attributes

testAttribute :: CommonKorePattern
testAttribute =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias =
                SymbolOrAlias
                    { symbolOrAliasConstructor = "test"
                    , symbolOrAliasParams = []
                    }
            , applicationChildren = []
            }

badHookAttribute :: CommonKorePattern
badHookAttribute =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = hookSymbol
            , applicationChildren = []
            }

expectError
    :: Show a
    => String
    -> Either (Error ParseError) a
    -> Assertion
expectError _ (Left _) = pure ()
expectError what (Right got) =
    assertFailure
    ("expected error parsing '" ++ what
     ++ "', but got: '" ++ show got ++ "'")

test_stepperAttributes :: [TestTree]
test_stepperAttributes =
    [ testCase "Parsing a constructor attribute"
        (assertEqual "[constructor{}()]"
            (Right Constructor { isConstructor = True })
            (Lens.view constructor <$> parse [constructorAttribute])
        )
    , testCase "Parsing a function attribute"
        (assertEqual "[function{}()]"
            (Right Function { isDeclaredFunction = True })
            (Lens.view function <$> parse [functionAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual "[functional{}()]"
            (Right Functional { isDeclaredFunctional = True })
            (Lens.view functional <$> parse [functionalAttribute])
        )
    , testCase "Parsing a hook attribute"
        (assertEqual "[function{}(),hook{}(\"builtin\")]"
            (Right Hook { getHook = Just "builtin" })
            (Lens.view hook <$> parse [ hookAttribute "builtin" ])
        )
    , testCase "Parsing an illegal hook attribute"
        (expectError "[hook{}()]"
            (parse [ badHookAttribute ])
        )
    , testCase "Parsing repeated hook attribute"
        (expectError
            "[function{}(),hook{}(\"BUILTIN.1\"),hook{}(\"BUILTIN.2\")]"
            (parse [ badHookAttribute ])
        )
    , testCase "Ignoring unknown attribute"
        (assertEqual "[test{}()]"
            (Right def)
            (parse [testAttribute])
        )
    , testCase "Testing parseAttributes"
        (assertEqual "[functional{}(),function{}(),hook{}(\"builtin\")]"
            (defaultStepperAttributes
                & Lens.set function (Function True)
                & Lens.set functional (Functional True)
                & Lens.set hook (Hook $ Just "builtin")
                & Right
            )
            (parse
                [ functionAttribute
                , functionalAttribute
                , testAttribute
                , hookAttribute "builtin"
                ]
            )
        )
    ]
