module Test.Kore.Attribute.Axiom.Concrete (
    test_concrete,
    test_concrete_select,
    test_concrete_selectx2,
    test_Attributes,
    test_parameters,
    test_duplicate,
    test_duplicate2,
    test_duplicate3,
    test_notfree,
    test_arguments,
) where

import qualified Data.Default as Default
import Kore.Attribute.Axiom.Concrete
import Kore.Attribute.Pattern.FreeVariables (
    freeVariable,
 )
import Kore.Syntax.Variable hiding (
    Concrete,
 )
import Prelude.Kore
import Test.Kore.Attribute.Parser
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit

parseConcrete ::
    FreeVariables VariableName ->
    Attributes ->
    Parser (Concrete VariableName)
parseConcrete freeVariables (Attributes attrs) =
    foldlM
        (flip $ parseConcreteAttribute freeVariables)
        Default.def
        attrs

test_concrete :: TestTree
test_concrete =
    testCase "[concrete{}()] :: Concrete" $
        expectSuccess Concrete{unConcrete = freeVars} $
            parseConcrete freeVars $ Attributes [concreteAttribute []]
  where
    freeVars = foldMap freeVariable [inject Mock.x, inject Mock.y]

test_concrete_select :: TestTree
test_concrete_select =
    testCase "[concrete{}(x:testSort)] :: Concrete" $
        expectSuccess Concrete{unConcrete = concreteVars} $
            parseConcrete freeVars $ Attributes [concreteAttribute [inject Mock.x]]
  where
    freeVars = foldMap freeVariable [inject Mock.x, inject Mock.y]
    concreteVars = freeVariable (inject Mock.x)

test_concrete_selectx2 :: TestTree
test_concrete_selectx2 =
    testCase "[concrete{}(x:testSort),concrete{}(z:testSort)] :: Concrete" $
        expectSuccess Concrete{unConcrete = concreteVars} $
            parseConcrete freeVars $
                Attributes
                    [ concreteAttribute [inject Mock.x]
                    , concreteAttribute [inject Mock.z]
                    ]
  where
    freeVars = foldMap freeVariable $ inject <$> [Mock.x, Mock.y, Mock.z]
    concreteVars = foldMap (freeVariable . inject) [Mock.x, Mock.z]

test_Attributes :: TestTree
test_Attributes =
    testCase "[concrete{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [concreteAttribute []]

test_notfree :: TestTree
test_notfree =
    testCase "[concrete{}(y:testSort)] -- not free" $
        expectFailure $
            parseConcrete freeVars $
                Attributes [concreteAttribute [inject Mock.y]]
  where
    freeVars = freeVariable (inject Mock.x)

test_duplicate :: TestTree
test_duplicate =
    testCase "[concrete{}(), concrete{}()]" $
        expectFailure $
            parseConcrete freeVars $
                Attributes [concreteAttribute [], concreteAttribute []]
  where
    freeVars = freeVariable (inject Mock.x)

test_duplicate2 :: TestTree
test_duplicate2 =
    testCase "[concrete{}(), concrete{}(x:testSort)]" $
        expectFailure $
            parseConcrete freeVars $
                Attributes [concreteAttribute [], concreteAttribute [inject Mock.x]]
  where
    freeVars = freeVariable (inject Mock.x)

test_duplicate3 :: TestTree
test_duplicate3 =
    testCase "[concrete{}(x:testSort), concrete{}(x:testSort)]" $
        expectFailure $
            parseConcrete freeVars $
                Attributes
                    [ concreteAttribute [inject Mock.x]
                    , concreteAttribute [inject Mock.x]
                    ]
  where
    freeVars = freeVariable (inject Mock.x)

test_arguments :: TestTree
test_arguments =
    testCase "[concrete{}(\"illegal\")]" $
        expectFailure $
            parseConcrete freeVars $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern concreteSymbol [attributeString "illegal"]
    freeVars = freeVariable (inject Mock.x)

test_parameters :: TestTree
test_parameters =
    testCase "[concrete{illegal}()]" $
        expectFailure $
            parseConcrete freeVars $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern_
            SymbolOrAlias
                { symbolOrAliasConstructor = concreteId
                , symbolOrAliasParams =
                    [SortVariableSort (SortVariable "illegal")]
                }
    freeVars = freeVariable (inject Mock.x)
