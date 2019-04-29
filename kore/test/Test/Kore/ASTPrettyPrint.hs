module Test.Kore.ASTPrettyPrint (test_astPrettyPrint) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Kore.AST.Pure
import           Kore.ASTPrettyPrint
import qualified Kore.Domain.Builtin as Domain

import Test.Kore

test_astPrettyPrint :: [TestTree]
test_astPrettyPrint =
    [ testCase "Char literal"
        (assertEqual ""
            "CharLiteralPattern (CharLiteral 'a')"
            (prettyPrintPattern (CharLiteralPattern (CharLiteral 'a')))
        )
    , testCase "Object unified variable"
        (assertEqual ""
            "Variable\n\
            \    { variableName = Id \"v\" AstLocationNone\n\
            \    , variableCounter = Nothing\n\
            \    , variableSort =\n\
            \        SortVariableSort (SortVariable (Id \"sv\" AstLocationNone))\n\
            \    }"
            (prettyPrintToString
                (Variable
                    { variableName = testId "v"
                    , variableCounter = mempty
                    , variableSort =
                        SortVariableSort (SortVariable (testId "sv"))
                    }
                )
            )
        )
    , testCase "Maybe - Just"
        (assertEqual ""
            "Just (Id \"v\" AstLocationNone)"
            (prettyPrintToString
                (Just (testId "v" :: Id))
            )
        )
    , testCase "Maybe - Nothing"
        (assertEqual ""
            "Nothing"
            (prettyPrintToString (Nothing :: Maybe Id))
        )
    ]

prettyPrintPattern
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable ParsedPattern
    -> String
prettyPrintPattern = prettyPrintToString
