module Test.Data.Kore.Step.StepperAttributes (test_stepperAttributes) where

import           Test.Tasty                            (TestTree)
import           Test.Tasty.HUnit                      (assertEqual, testCase)

import           Data.Default                          (def)


import           Test.Data.Kore.Comparators            ()

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore                    (CommonKorePattern)
import           Data.Kore.AST.PureToKore              (patternPureToKore)
import           Data.Kore.AST.Sentence                (Attributes (..))
import           Data.Kore.ASTUtils.SmartPatterns
import           Data.Kore.IndexedModule.IndexedModule (ParsedAttributes (..))
import           Data.Kore.Step.StepperAttributes


parseStepperAttributes :: [CommonKorePattern] -> StepperAttributes
parseStepperAttributes atts = parseAttributes (Attributes atts)

test_stepperAttributes :: [TestTree]
test_stepperAttributes =
    [ testCase "Parsing a constructor attribute"
        (assertEqual ""
            def {isConstructor = True}
            (parseStepperAttributes [constructorAttribute])
        )
    , testCase "Parsing a function attribute"
        (assertEqual ""
            def {isFunction = True}
            (parseStepperAttributes [functionAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual ""
            def {isFunctional = True}
            (parseStepperAttributes [functionalAttribute])
        )
    , testCase "Parsing a functional attribute"
        (assertEqual ""
            def {isFunctional = True}
            (parseStepperAttributes [functionalAttribute])
        )
    , testCase "Ignoring unknown attribute"
        (assertEqual ""
            def
            (parseStepperAttributes
                [patternPureToKore (StringLiteral_ (StringLiteral "test"))]
            )
        )
    , testCase "Testing parseAttributes"
        (assertEqual ""
            StepperAttributes
                { isFunction = True
                , isFunctional = True
                , isConstructor = False
                }
            (parseStepperAttributes
                [ functionAttribute
                , functionalAttribute
                , patternPureToKore (StringLiteral_ (StringLiteral "test"))
                ]
            )
        )
    ]
