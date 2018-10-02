module Test.Kore.Step.Condition.Evaluator (test_conditionEvaluator) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Map as Map
import           Data.Map ( Map )

import           Data.Proxy
import           Data.Reflection

import           Kore.AST.Sentence
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML

import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns

import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error

import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools

import           Kore.Step.StepperAttributes
import           Test.Kore.Step.Simplifier

import           Kore.Error

import           Kore.Step.ExpandedPattern
import qualified Kore.Step.Condition.Evaluator as Eval
import           Kore.Step.Simplification.Data

import           Kore.Predicate.Predicate

import qualified Kore.Builtin as Builtin

import           Test.Kore.Builtin.Bool 
                   (boolDefinition, boolModuleName, boolSort)

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
                    flip runSimplifier 0 $ 
                    Eval.evaluate
                    (mockSimplifier [])
                    ( wrapPredicate 
                        (mkAnd a (mkNot a) :: CommonPurePattern Object)
                    )
                )
                ( PredicateSubstitution 
                    { predicate = makeFalsePredicate :: CommonPredicate Object
                    , substitution = []
                    }
                )
            )
        ]
    where a :: Given (SymbolOrAliasSorts Object) => CommonPurePattern Object
          a = V $ "a" `varS` boolSort

