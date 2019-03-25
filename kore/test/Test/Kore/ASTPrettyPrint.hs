module Test.Kore.ASTPrettyPrint (test_astPrettyPrint) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Kore.AST.Kore
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
            (  "UnifiedObject Variable\n"
            ++ "    { variableName = (Id \"v\" AstLocationNone) :: Id Object\n"
            ++ "    , variableCounter = Nothing\n"
            ++ "    , variableSort =\n"
            ++ "        SortVariableSort (SortVariable ((Id \"sv\" AstLocationNone) :: Id Object))\n"
            ++ "    }"
            )
            (prettyPrintToString
                (UnifiedObject Variable
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
            "Just ((Id \"v\" AstLocationNone) :: Id Object)"
            (prettyPrintToString
                (Just (testId "v" :: Id Object))
            )
        )
    , testCase "Maybe - Nothing"
        (assertEqual ""
            "Nothing"
            (prettyPrintToString (Nothing :: Maybe (Id Object)))
        )
    ]

prettyPrintPattern
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable CommonKorePattern
    -> String
prettyPrintPattern = prettyPrintToString
