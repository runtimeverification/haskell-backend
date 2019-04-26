module Test.Kore.Contains
    ( AssertContains (..)
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Data.Map
                 ( Map )
import qualified Data.Map as Map

import qualified Kore.AST.Identifier as Kore
                 ( Id )
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Step.SMT.AST as AST
                 ( Declarations (Declarations), Sort, Symbol )
import qualified Kore.Step.SMT.AST as AST.DoNotUse

import Test.Tasty.HUnit.Extensions

class AssertContains container contained where
    assertContains :: HasCallStack => container -> contained -> IO ()

    assertContainedIn :: HasCallStack => contained -> container -> IO ()
    assertContainedIn = flip assertContains

    testContains :: HasCallStack => container -> contained -> TestTree
    testContains container contained =
        testCase "containment" $ assertContains container contained

    testContainedIn :: HasCallStack => contained -> container -> TestTree
    testContainedIn = flip testContains

instance (Ord a, Show a, EqualWithExplanation b)
    => AssertContains (Map a b) (a, b)
  where
    assertContains actualContainer (expectedKey, expectedValue) =
        case Map.lookup expectedKey actualContainer of
            Nothing ->
                assertFailure
                    (  "Key (" ++ show expectedKey
                    ++ ") not found in (" ++ show (Map.keysSet actualContainer)
                    ++ ")"
                    )
            Just actualValue ->
                assertEqualWithExplanation "" expectedValue actualValue

instance
    (EqualWithExplanation (AST.Sort sort symbol name))
    => AssertContains
        (AST.Declarations sort symbol name)
        (Kore.Id Object, AST.Sort sort symbol name)
  where
    assertContains AST.Declarations {sorts} =
        assertContains sorts

instance
    (EqualWithExplanation (AST.Symbol sort name))
    => AssertContains
        (AST.Declarations sort symbol name)
        (Kore.Id Object, AST.Symbol sort name)
  where
    assertContains AST.Declarations {symbols} =
        assertContains symbols
