module Test.Kore.Attribute.Symbol.NoEvaluators (
    test_noEvaluators,
    test_Attributes,
    test_duplicate,
    test_arguments,
    test_parameters,
) where

import Kore.Attribute.Symbol.NoEvaluators
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseNoEvaluators :: Attributes -> Parser NoEvaluators
parseNoEvaluators = parseAttributes

test_noEvaluators :: TestTree
test_noEvaluators =
    testCase "[no-evaluators{}()] :: NoEvaluators" $
        expectSuccess NoEvaluators{hasNoEvaluators = True} $
            parseNoEvaluators $ Attributes [noEvaluatorsAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[no-evaluators{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [noEvaluatorsAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[no-evaluators{}(), no-evaluators{}()]" $
        expectFailure $
            parseNoEvaluators $
                Attributes [noEvaluatorsAttribute, noEvaluatorsAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[no-evaluators{}(\"illegal\")]" $
        expectFailure $
            parseNoEvaluators $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern noEvaluatorsSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[no-evaluators{illegal}()]" $
        expectFailure $
            parseNoEvaluators $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = noEvaluatorsId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
