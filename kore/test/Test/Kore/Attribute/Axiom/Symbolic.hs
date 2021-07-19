module Test.Kore.Attribute.Axiom.Symbolic (
    test_symbolic,
    test_symbolic_select,
    test_symbolic_selectx2,
    test_Attributes,
    test_parameters,
    test_duplicate,
    test_duplicate2,
    test_duplicate3,
    test_notfree,
    test_arguments,
) where

import qualified Data.Default as Default
import Kore.Attribute.Axiom.Symbolic
import Kore.Attribute.Pattern.FreeVariables (
    freeVariable,
 )
import Kore.Syntax.Variable
import Prelude.Kore
import Test.Kore.Attribute.Parser
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit

parseSymbolic ::
    FreeVariables VariableName ->
    Attributes ->
    Parser (Symbolic VariableName)
parseSymbolic freeVariables (Attributes attrs) =
    foldlM
        (flip $ parseSymbolicAttribute freeVariables)
        Default.def
        attrs

test_symbolic :: TestTree
test_symbolic =
    testCase "[symbolic{}()] :: Symbolic" $
        expectSuccess Symbolic{unSymbolic = freeVars} $
            parseSymbolic freeVars $ Attributes [symbolicAttribute []]
  where
    freeVars = foldMap freeVariable [inject Mock.x, inject Mock.y]

test_symbolic_select :: TestTree
test_symbolic_select =
    testCase "[symbolic{}(x:testSort)] :: Symbolic" $
        expectSuccess Symbolic{unSymbolic = symbolicVars} $
            parseSymbolic freeVars $ Attributes [symbolicAttribute [inject Mock.x]]
  where
    freeVars = foldMap freeVariable [inject Mock.x, inject Mock.y]
    symbolicVars = freeVariable (inject Mock.x)

test_symbolic_selectx2 :: TestTree
test_symbolic_selectx2 =
    testCase "[symbolic{}(x:testSort),symbolic{}(z:testSort)] :: Symbolic" $
        expectSuccess Symbolic{unSymbolic = symbolicVars} $
            parseSymbolic freeVars $
                Attributes
                    [ symbolicAttribute [inject Mock.x]
                    , symbolicAttribute [inject Mock.z]
                    ]
  where
    freeVars = foldMap freeVariable $ inject <$> [Mock.x, Mock.y, Mock.z]
    symbolicVars = foldMap (freeVariable . inject) [Mock.x, Mock.z]

test_Attributes :: TestTree
test_Attributes =
    testCase "[symbolic{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [symbolicAttribute []]

test_notfree :: TestTree
test_notfree =
    testCase "[symbolic{}(y:testSort)] -- not free" $
        expectFailure $
            parseSymbolic freeVars $
                Attributes [symbolicAttribute [inject Mock.y]]
  where
    freeVars = freeVariable (inject Mock.x)

test_duplicate :: TestTree
test_duplicate =
    testCase "[symbolic{}(), symbolic{}()]" $
        expectFailure $
            parseSymbolic freeVars $
                Attributes [symbolicAttribute [], symbolicAttribute []]
  where
    freeVars = freeVariable (inject Mock.x)

test_duplicate2 :: TestTree
test_duplicate2 =
    testCase "[symbolic{}(), symbolic{}(x:testSort)]" $
        expectFailure $
            parseSymbolic freeVars $
                Attributes [symbolicAttribute [], symbolicAttribute [inject Mock.x]]
  where
    freeVars = freeVariable (inject Mock.x)

test_duplicate3 :: TestTree
test_duplicate3 =
    testCase "[symbolic{}(x:testSort), symbolic{}(x:testSort)]" $
        expectFailure $
            parseSymbolic freeVars $
                Attributes
                    [ symbolicAttribute [inject Mock.x]
                    , symbolicAttribute [inject Mock.x]
                    ]
  where
    freeVars = freeVariable (inject Mock.x)

test_arguments :: TestTree
test_arguments =
    testCase "[symbolic{}(\"illegal\")]" $
        expectFailure $
            parseSymbolic freeVars $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern symbolicSymbol [attributeString "illegal"]
    freeVars = freeVariable (inject Mock.x)

test_parameters :: TestTree
test_parameters =
    testCase "[symbolic{illegal}()]" $
        expectFailure $
            parseSymbolic freeVars $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern_
            SymbolOrAlias
                { symbolOrAliasConstructor = symbolicId
                , symbolOrAliasParams =
                    [SortVariableSort (SortVariable "illegal")]
                }
    freeVars = freeVariable (inject Mock.x)
