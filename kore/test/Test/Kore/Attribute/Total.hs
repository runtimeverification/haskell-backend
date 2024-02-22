module Test.Kore.Attribute.Total (
    test_total,
    test_Attributes,
    -- TODO: Uncomment after frontend will be fixed
    -- See comment to the test below
    -- test_duplicate,
    test_parameters,
    test_arguments,
) where

import Kore.Attribute.Total
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseTotal :: Attributes -> Parser Total
parseTotal = parseAttributes

test_total :: TestTree
test_total =
    testCase "[total{}()] :: Total" $
        expectSuccess Total{isDeclaredTotal = True} $
            parseTotal $
                Attributes [totalAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[total{}()] :: Attributes" $
        expectSuccess attrs $
            parseAttributes attrs
  where
    attrs = Attributes [totalAttribute]

{- TODO: Uncomment the test after frontend will be fixed
   Now duplicate total attributes are allowed because frontend
   when rewrites @functional@ attribute sets both @functional@
   and @total@ which both are parsed as @total@
-}
-- test_duplicate :: TestTree
-- test_duplicate =
--     testCase "[total{}(), total{}()]" $
--         expectFailure $
--             parseTotal $
--                 Attributes [totalAttribute, totalAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[total{}(\"illegal\")]" $
        expectFailure $
            parseTotal $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern totalSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[total{illegal}()]" $
        expectFailure $
            parseTotal $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = totalId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
