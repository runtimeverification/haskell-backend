module Test.Kore.Step.Condition.Evaluator (test_conditionEvaluator) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
import           Data.Reflection

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.SMT.Config
import qualified Kore.Step.Condition.Evaluator as Eval
import           Kore.Step.ExpandedPattern
import           Kore.Step.StepperAttributes

import           Test.Kore.Builtin.Bool
                 ( boolDefinition, boolModuleName, boolSort )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.Simplifier

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
Right indexedModules = verify' boolDefinition

verify'
    :: KoreDefinition
    -> Either (Kore.Error.Error VerifyError)
        (Map ModuleName (KoreIndexedModule StepperAttributes))
verify' = verifyAndIndexDefinition attrVerify Builtin.koreVerifiers
  where
    attrVerify = defaultAttributesVerification Proxy

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup boolModuleName indexedModules

tools :: MetadataTools Object StepperAttributes
tools = extractMetadataTools indexedModule

test_conditionEvaluator :: TestTree
test_conditionEvaluator =
    testGroup
        "Condition Evaluator"
        [ testCase "a /\\ ~a"
            (assertEqual ""
                ( fst $ fst $
                    give tools $
                    give (symbolOrAliasSorts tools) $
                    flip (runSimplifierTest $ SMTTimeOut 1000) 0 $
                    Eval.evaluate
                        (Mock.substitutionSimplifier tools)
                        (mockSimplifier [])
                        ( wrapPredicate
                            (mkAnd a (mkNot a) :: CommonPurePattern Object)
                        )
                )
                PredicateSubstitution
                    { predicate = makeFalsePredicate :: CommonPredicate Object
                    , substitution = []
                    }
            )
        ]
    where a :: Given (SymbolOrAliasSorts Object) => CommonPurePattern Object
          a = V $ "a" `varS` boolSort
