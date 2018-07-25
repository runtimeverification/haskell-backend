module Test.Kore.ASTPrettyPrint (test_astPrettyPrint) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Data.Functor.Foldable
       ( Fix (..) )

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.ASTPrettyPrint
import Kore.Implicit.ImplicitSorts
       ( charMetaSort )
import Kore.MetaML.AST

import Test.Kore

test_astPrettyPrint :: [TestTree]
test_astPrettyPrint =
    [ testCase "Char literal"
        (assertEqual ""
            "CharLiteralPattern (CharLiteral 'a')"
            (prettyPrintPattern (CharLiteralPattern (CharLiteral 'a')))
        )
    , testCase "Meta unified variable"
        (assertEqual ""
            (  "UnifiedMeta Variable\n"
            ++ "    { variableName = (Id \"#v\" AstLocationNone) :: Id Meta\n"
            ++ "    , variableSort =\n"
            ++ "        SortVariableSort (SortVariable ((Id \"#sv\" AstLocationNone) :: Id Meta))\n"
            ++ "    }"
            )
            (prettyPrintToString
                (UnifiedMeta Variable
                    { variableName = testId "#v"
                    , variableSort =
                        SortVariableSort (SortVariable (testId "#sv"))
                    }
                )
            )
        )
    , testCase "Object unified variable"
        (assertEqual ""
            (  "UnifiedObject Variable\n"
            ++ "    { variableName = (Id \"v\" AstLocationNone) :: Id Object\n"
            ++ "    , variableSort =\n"
            ++ "        SortVariableSort (SortVariable ((Id \"sv\" AstLocationNone) :: Id Object))\n"
            ++ "    }"
            )
            (prettyPrintToString
                (UnifiedObject Variable
                    { variableName = testId "v"
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
        , testCase "MetaMLPattern - Top"
        (assertEqual ""
            (  "Fix (TopPattern (Top (SortActualSort SortActual\n"
            ++ "    { sortActualName = (Id \"#Char\" AstLocationNone) :: Id Meta\n"
            ++ "    , sortActualSorts = []\n"
            ++ "    })))"
            )
            (prettyPrintToString
                (Fix (TopPattern (Top charMetaSort))
                :: MetaMLPattern Variable
                )
            )
        )
    ]

prettyPrintPattern
    :: MetaOrObject level => Pattern level Variable CommonKorePattern -> String
prettyPrintPattern = prettyPrintToString
