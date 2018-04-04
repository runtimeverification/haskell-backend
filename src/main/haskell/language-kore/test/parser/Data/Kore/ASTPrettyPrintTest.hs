module Data.Kore.ASTPrettyPrintTest (astPrettyPrintTests) where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.Implicit.ImplicitSorts (charMetaSort)
import           Data.Kore.MetaML.AST

import           Data.Fix                         (Fix (..))

astPrettyPrintTests :: TestTree
astPrettyPrintTests =
    testGroup "PrettyPrint tests"
        [ testCase "Char literal"
            (assertEqual ""
                "CharLiteralPattern (CharLiteral 'a')"
                (prettyPrintPattern (CharLiteralPattern (CharLiteral 'a')))
            )
        , testCase "Meta unified variable"
            (assertEqual ""
                (  "MetaVariable Variable\n"
                ++ "    { variableName = Id Meta \"#v\"\n"
                ++ "    , variableSort =\n"
                ++ "        SortVariableSort (SortVariable (Id Meta \"#sv\"))\n"
                ++ "    }"
                )
                (prettyPrintToString
                    (MetaVariable Variable
                        { variableName = Id "#v"
                        , variableSort =
                            SortVariableSort (SortVariable (Id "#sv"))
                        }
                    )
                )
            )
        , testCase "Object unified variable"
            (assertEqual ""
                (  "ObjectVariable Variable\n"
                ++ "    { variableName = Id Object \"v\"\n"
                ++ "    , variableSort =\n"
                ++ "        SortVariableSort (SortVariable (Id Object \"sv\"))\n"
                ++ "    }"
                )
                (prettyPrintToString
                    (ObjectVariable Variable
                        { variableName = Id "v"
                        , variableSort =
                            SortVariableSort (SortVariable (Id "sv"))
                        }
                    )
                )
            )
        , testCase "Maybe - Just"
            (assertEqual ""
                "Just (Id Object \"v\")"
                (prettyPrintToString
                    (Just (Id "v" :: Id Object))
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
                ++ "    { sortActualName = Id Meta \"#Char\"\n"
                ++ "    , sortActualSorts = []\n"
                ++ "    })))"
                )
                (prettyPrintToString
                    (Fix (TopPattern (Top charMetaSort))
                    :: MetaMLPattern Variable
                    )
                )
            )
        , testCase "SentenceMetaPattern - Top"
            (assertEqual ""
                (  "SentenceMetaPattern (Fix (TopPattern (Top (SortActualSort SortActual\n"
                ++ "    { sortActualName = Id Meta \"#Char\"\n"
                ++ "    , sortActualSorts = []\n"
                ++ "    }))))"
                )
                (prettyPrintToString
                    (SentenceMetaPattern (Fix (TopPattern (Top charMetaSort)))
                    :: SentenceMetaPattern Variable
                    )
                )
            )
        ]

prettyPrintPattern
    :: MetaOrObject level => Pattern level Variable UnifiedPattern -> String
prettyPrintPattern = prettyPrintToString
