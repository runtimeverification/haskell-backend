module Test.Kore.Step.StepperAttributes (test_stepperAttributes) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( Assertion, assertEqual, assertFailure, testCase )

import Data.Default
       ( def )

import Test.Kore.Comparators ()

import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.Sentence
                 ( Attributes (..) )
import           Kore.Attribute.Parser
                 ( parseAttributes )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Builtin.Hook
import           Kore.Error
                 ( Error )
import           Kore.Implicit.Attributes
                 ( keyOnlyAttribute )
import           Kore.Step.StepperAttributes


parseStepperAttributes :: [CommonKorePattern] -> Either (Error Attribute.ParseError) StepperAttributes
parseStepperAttributes atts = parseAttributes (Attributes atts)

testAttribute :: CommonKorePattern
testAttribute = keyOnlyAttribute "test"

badHookAttribute :: CommonKorePattern
badHookAttribute = keyOnlyAttribute "hook"

expectError :: Show a => String -> Either (Error Attribute.ParseError) a -> Assertion
expectError _ (Left _) = pure ()
expectError what (Right got) =
    assertFailure
    ("expected error parsing '" ++ what
     ++ "', but got: '" ++ show got ++ "'")

test_stepperAttributes :: [TestTree]
test_stepperAttributes =
    [ testCase "Parsing a constructor attribute"
        (assertEqual "[constructor{}()]"
            (Right True)
            (isConstructor <$> parseStepperAttributes [constructorAttribute])
        )
    , testCase "Parsing a function attribute"
        (assertEqual "[function{}()]"
            (Right True)
            (isFunction <$> parseStepperAttributes [functionAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual "[functional{}()]"
            (Right True)
            (isFunctional <$> parseStepperAttributes [functionalAttribute])
        )
    , testCase "Parsing a hook attribute"
        (assertEqual "[function{}(),hook{}(\"builtin\")]"
            (Right ((Hook . Just) "builtin"))
            (hook <$>
                parseStepperAttributes
                [ hookAttribute "builtin" ]
            )
        )
    , testCase "Parsing an illegal hook attribute"
        (expectError "[hook{}()]"
            (parseStepperAttributes [ badHookAttribute ])
        )
    , testCase "Parsing repeated hook attribute"
        (expectError
            "[function{}(),hook{}(\"BUILTIN.1\"),hook{}(\"BUILTIN.2\")]"
            (parseStepperAttributes [ badHookAttribute ])
        )
    , testCase "Ignoring unknown attribute"
        (assertEqual "[test{}()]"
            (Right def)
            (parseStepperAttributes
                [testAttribute]
            )
        )
    , testCase "Testing parseAttributes"
        (assertEqual "[functional{}(),function{}(),hook{}(\"builtin\")]"
            (Right StepperAttributes
                { isFunction = True
                , isFunctional = True
                , isConstructor = False
                , hook = (Hook . Just) "builtin"
                })
            (parseStepperAttributes
                [ functionAttribute
                , functionalAttribute
                , testAttribute
                , hookAttribute "builtin"
                ]
            )
        )
    ]
