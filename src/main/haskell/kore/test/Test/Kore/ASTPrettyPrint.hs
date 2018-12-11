module Test.Kore.ASTPrettyPrint (test_astPrettyPrint) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Kore.AST.Kore
import           Kore.ASTPrettyPrint
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.Implicit.ImplicitSorts
                 ( charMetaSort )
import           Kore.MetaML.AST

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
            "PurePattern\n\
            \    { getPurePattern = CofreeT\n\
            \        { runCofreeT = Identity\n\
            \            { runIdentity = Null :< TopPattern (Top (SortActualSort SortActual\n\
            \                { sortActualName = (Id \"#Char\" AstLocationNone) :: Id Meta\n\
            \                , sortActualSorts = []\n\
            \                }))\n\
            \            }\n\
            \        }\n\
            \    }"
            (prettyPrintToString (Top_ charMetaSort :: CommonMetaPattern))
        )
    ]

prettyPrintPattern
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable CommonKorePattern
    -> String
prettyPrintPattern = prettyPrintToString
