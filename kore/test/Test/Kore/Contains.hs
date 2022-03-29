module Test.Kore.Contains (
    AssertContains (..),
) where

import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Kore.Rewrite.SMT.AST qualified as AST (
    Declarations (Declarations),
    Sort,
    Symbol,
 )
import Kore.Rewrite.SMT.AST qualified as AST.DoNotUse
import Kore.Syntax.Id qualified as Kore (
    Id,
 )
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit.Ext

class AssertContains container contained where
    assertContains :: HasCallStack => container -> contained -> IO ()

    assertContainedIn :: HasCallStack => contained -> container -> IO ()
    assertContainedIn = flip assertContains

    testContains :: HasCallStack => container -> contained -> TestTree
    testContains container contained =
        testCase "containment" $ assertContains container contained

    testContainedIn :: HasCallStack => contained -> container -> TestTree
    testContainedIn = flip testContains

instance
    (Ord a, Show a, Diff b) =>
    AssertContains (Map a b) (a, b)
    where
    assertContains actualContainer (expectedKey, expectedValue) =
        case Map.lookup expectedKey actualContainer of
            Nothing ->
                assertFailure
                    ( "Key (" ++ show expectedKey
                        ++ ") not found in ("
                        ++ show (Map.keysSet actualContainer)
                        ++ ")"
                    )
            Just actualValue ->
                assertEqual "" expectedValue actualValue

instance
    (Diff (AST.Sort sort symbol name)) =>
    AssertContains
        (AST.Declarations sort symbol name)
        (Kore.Id, AST.Sort sort symbol name)
    where
    assertContains AST.Declarations{sorts} =
        assertContains sorts

instance
    (Diff (AST.Symbol sort name)) =>
    AssertContains
        (AST.Declarations sort symbol name)
        (Kore.Id, AST.Symbol sort name)
    where
    assertContains AST.Declarations{symbols} =
        assertContains symbols
