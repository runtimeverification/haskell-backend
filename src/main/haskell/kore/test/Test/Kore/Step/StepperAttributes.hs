module Test.Kore.Step.StepperAttributes (test_stepperAttributes) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

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
import           Kore.Error
                 ( Error )
import           Kore.Implicit.Attributes
                 ( keyOnlyAttribute )
import           Kore.Step.StepperAttributes


parseStepperAttributes :: [CommonKorePattern] -> Either (Error Attribute.ParseError) StepperAttributes
parseStepperAttributes atts = parseAttributes (Attributes atts)

testAttribute :: CommonKorePattern
testAttribute = keyOnlyAttribute "test"

test_stepperAttributes :: [TestTree]
test_stepperAttributes =
    [ testCase "Parsing a constructor attribute"
        (assertEqual ""
            (Right def {isConstructor = True})
            (parseStepperAttributes [constructorAttribute])
        )
    , testCase "Parsing a function attribute"
        (assertEqual ""
            (Right def {isFunction = True})
            (parseStepperAttributes [functionAttribute])
        )
    , testCase "Testing isFunction"
        (assertEqual ""
            (Right True)
            (isFunction <$> parseStepperAttributes [functionAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual ""
            (Right def {isFunctional = True})
            (parseStepperAttributes [functionalAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual ""
            (Right def {isFunctional = True})
            (parseStepperAttributes [functionalAttribute])
        )
    , testCase "Ignoring unknown attribute"
        (assertEqual ""
            (Right def)
            (parseStepperAttributes
                [testAttribute]
            )
        )
    , testCase "Testing parseAttributes"
        (assertEqual ""
            (Right StepperAttributes
                { isFunction = True
                , isFunctional = True
                , isConstructor = False
                })
            (parseStepperAttributes
                [ functionAttribute
                , functionalAttribute
                , testAttribute
                ]
            )
        )
    ]
