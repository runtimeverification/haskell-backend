module Test.Kore.Rewrite.SMT.Representation.Helpers (
    declarationsAre,
    smtForSortIs,
    smtForSymbolIs,
    testsForModule,
) where

import Data.Map.Strict qualified as Map
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Rewrite.SMT.AST qualified as AST (
    Declarations (Declarations),
    Sort (Sort),
    Symbol (Symbol),
    symbolSmtFromSortArgs,
 )
import Kore.Rewrite.SMT.AST qualified as AST.DoNotUse
import Kore.Rewrite.SMT.Representation.Sorts qualified as AST (
    sortSmtFromSortArgs,
 )
import Kore.Syntax.Id qualified as Kore (
    Id,
 )
import Prelude.Kore
import SMT.AST qualified as AST (
    showSExpr,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

testsForModule ::
    String ->
    (VerifiedModule Attribute.Symbol -> AST.Declarations sort symbol name) ->
    VerifiedModule Attribute.Symbol ->
    [AST.Declarations sort symbol name -> TestTree] ->
    TestTree
testsForModule name functionToTest indexedModule tests =
    testGroup name (map (\f -> f declarations) tests)
  where
    declarations = functionToTest indexedModule

declarationsAre ::
    ( HasCallStack
    , Debug sort
    , Diff sort
    , Debug symbol
    , Diff symbol
    , Debug name
    , Diff name
    ) =>
    AST.Declarations sort symbol name ->
    AST.Declarations sort symbol name ->
    TestTree
declarationsAre expected actual =
    testCase "declarationsAre" (assertEqual "" expected actual)

smtForSortIs ::
    HasCallStack =>
    Kore.Id ->
    String ->
    AST.Declarations sort symbol name ->
    TestTree
smtForSortIs
    sortId
    expectedSExpr
    AST.Declarations{sorts} =
        testCase "smtForSortIs" $
            case Map.lookup sortId sorts of
                Nothing ->
                    assertFailure
                        ( "Key (" ++ show sortId
                            ++ ") not found in ("
                            ++ show (Map.keysSet sorts)
                            ++ ")"
                        )
                Just AST.Sort{sortData} ->
                    assertEqual
                        ""
                        (Just expectedSExpr)
                        (AST.showSExpr <$> AST.sortSmtFromSortArgs sortData Map.empty [])

smtForSymbolIs ::
    HasCallStack =>
    Kore.Id ->
    String ->
    AST.Declarations sort symbol name ->
    TestTree
smtForSymbolIs
    sortId
    expectedSExpr
    AST.Declarations{symbols} =
        testCase "smtForSymbolIs" $
            case Map.lookup sortId symbols of
                Nothing ->
                    assertFailure
                        ( "Key (" ++ show sortId
                            ++ ") not found in ("
                            ++ show (Map.keysSet symbols)
                            ++ ")"
                        )
                Just AST.Symbol{symbolData} ->
                    assertEqual
                        ""
                        (Just expectedSExpr)
                        (AST.showSExpr <$> AST.symbolSmtFromSortArgs symbolData Map.empty [])
