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

import Kore.AST.Kore
import Kore.AST.Sentence
       ( Attributes (..) )
import Kore.Attribute.Hook
import Kore.Attribute.Parser
       ( ParseError, parseAttributes )
import Kore.Error
       ( Error )
import Kore.Step.StepperAttributes

parse
    :: [CommonKorePattern]
    -> Either (Error ParseError) StepperAttributes
parse = parseAttributes . Attributes

testAttribute :: CommonKorePattern
testAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias =
                SymbolOrAlias
                    { symbolOrAliasConstructor = "test" :: Id Object
                    , symbolOrAliasParams = []
                    }
            , applicationChildren = []
            }

badHookAttribute :: CommonKorePattern
badHookAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = hookSymbol :: SymbolOrAlias Object
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
            (constructor <$> parse [constructorAttribute])
        )
    , testCase "Parsing a function attribute"
        (assertEqual "[function{}()]"
            (Right Function { isDeclaredFunction = True })
            (function <$> parse [functionAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual "[functional{}()]"
            (Right Functional { isDeclaredFunctional = True })
            (functional <$> parse [functionalAttribute])
        )
    , testCase "Parsing a hook attribute"
        (assertEqual "[function{}(),hook{}(\"builtin\")]"
            (Right Hook { getHook = Just "builtin" })
            (hook <$> parse [ hookAttribute "builtin" ])
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
                & Lens.set lensFunction (Function True)
                & Lens.set lensFunctional (Functional True)
                & Lens.set lensHook (Hook $ Just "builtin")
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
