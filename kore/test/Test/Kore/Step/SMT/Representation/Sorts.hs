module Test.Kore.Step.SMT.Representation.Sorts where

import Test.Tasty

import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors
    ( indexBySort
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.Int as Int
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.Step.SMT.AST as AST
    ( Declarations
    , Encodable (AlreadyEncoded)
    , Sort
    , SortReference
    , SymbolReference
    )
import Kore.Step.SMT.Representation.Sorts
import qualified Kore.Syntax.Id as Kore
    ( Id
    )

import Test.Kore
    ( testId
    )
import Test.Kore.Contains
import Test.Kore.Step.SMT.Builders
    ( constructor
    , emptyModule
    , functional
    , hook
    , indexModule
    , koreSort
    , sortDeclaration
    , symbolDeclaration
    )
import Test.Kore.Step.SMT.Helpers
    ( constructorAxiom
    )
import Test.Kore.Step.SMT.Representation.Builders
    ( emptyDeclarations
    , unresolvedConstructorArg
    , unresolvedDataMap
    , unresolvedIndirectSortMap
    , unresolvedSortConstructor
    , unresolvedSortMap
    )
import Test.Kore.Step.SMT.Representation.Helpers
    ( declarationsAre
    , smtForSortIs
    )
import qualified Test.Kore.Step.SMT.Representation.Helpers as Helpers
    ( testsForModule
    )
import Test.Kore.With
    ( with
    )
import Test.Tasty.HUnit.Ext

test_sortParsing :: [TestTree]
test_sortParsing =
    [ testsForModule "Empty definition"
        (indexModule $ emptyModule "m")
        [declarationsAre
            (emptyDeclarations
                `with` unresolvedSortMap "#String"
            )
        ]
    , testsForModule "Definition with simple sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` sortDeclaration "T"
        )
        [ inDeclarations (unresolvedSortMap "S")
        , inDeclarations (unresolvedSortMap "T")
        , smtForSortIs "S" "|HB_S|"
        , smtForSortIs "T" "|HB_T|"
        ]
    , testsForModule "Definition with constructor-based sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` sortDeclaration "T"
            `with`
                (symbolDeclaration "C" "S" [] `with` [functional, constructor])
            `with` constructorAxiom "S" [("C", [])]
        )
        [ inDeclarations
            (unresolvedDataMap "S"
                `with` unresolvedSortConstructor "C"
            )
        , inDeclarations (unresolvedSortMap "T")
        , smtForSortIs "S" "|HB_S|"
        , smtForSortIs "T" "|HB_T|"
        ]
    , testsForModule "Definition with complex constructor-based sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" [] `with` [functional, constructor])
            `with`
                (symbolDeclaration "D" "S" ["S"]
                    `with` [functional, constructor]
                )
            `with` constructorAxiom "S" [("C", []), ("D", ["S"])]
        )
        [ inDeclarations
            (unresolvedDataMap "S"
                `with`
                    (unresolvedSortConstructor "D"
                        `with` unresolvedConstructorArg "D1" (koreSort "S")
                    )
                `with` unresolvedSortConstructor "C"
            )
        , smtForSortIs "S" "|HB_S|"
        ]
    , testsForModule "Definition with builtin sorts"
        (indexModule $ emptyModule "m"
            `with` (sortDeclaration "Integer" `with` hook Int.sort)
        )
        [ inDeclarations
            (unresolvedIndirectSortMap
                (testId "Integer") (AST.AlreadyEncoded "Int")
            )
        , smtForSortIs (testId "Integer") "Int"
        ]
    ]
  where
    inDeclarations
        ::  ( HasCallStack
            , Diff (AST.Sort sort symbol name)
            )
        => (Kore.Id, AST.Sort sort symbol name)
        -> AST.Declarations sort symbol name
        -> TestTree
    inDeclarations = testContainedIn

testsForModule
    :: String
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
    ->  [  AST.Declarations AST.SortReference AST.SymbolReference AST.Encodable
        -> TestTree
        ]
    -> TestTree
testsForModule name =
    Helpers.testsForModule name build
  where
    build m = buildRepresentations m (Attribute.Constructors.indexBySort m)
