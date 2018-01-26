module Data.Kore.ASTVerifier.ASTVerifierTest (astVerifierTests) where

import           Test.Tasty                      (TestTree, testGroup)

import Data.Kore.ASTVerifier.DefinitionVerifierTest

astVerifierTests :: TestTree
astVerifierTests =
    testGroup
        " AST Verifier Unit Tests"
        [ definitionVerifierTests
        ]
