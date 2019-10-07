module Test.Kore.Step.SMT.Representation.Symbols where

import Test.Tasty

import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.Int as Int
import Kore.Debug
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.Step.SMT.AST as AST
    ( Declarations
    , Encodable
    , SortReference
    , Symbol
    , SymbolReference
    )
import Kore.Step.SMT.Representation.Symbols
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
    , smthook
    , smtlib
    , sortDeclaration
    , symbolDeclaration
    )
import Test.Kore.Step.SMT.Helpers
    ( constructorAxiom
    )
import Test.Kore.Step.SMT.Representation.Builders
    ( emptyDeclarations
    , unresolvedConstructorSymbolMap
    , unresolvedSmthookSymbolMap
    , unresolvedSmtlibSymbolMap
    )
import Test.Kore.Step.SMT.Representation.Helpers
    ( declarationsAre
    , smtForSymbolIs
    )
import qualified Test.Kore.Step.SMT.Representation.Helpers as Helpers
    ( testsForModule
    )
import Test.Kore.With
    ( with
    )
import Test.Tasty.HUnit.Ext

test_symbolParsing :: [TestTree]
test_symbolParsing =
    [ testsForModule "Empty definition"
        (indexModule $ emptyModule "m")
        [declarationsAre emptyDeclarations
        ]
    , testsForModule "Definition with constructors"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with`
                (symbolDeclaration "C" "S" [] `with` [functional, constructor])
            `with` constructorAxiom "S" [("C", [])]
        )
        [ inDeclarations
            (unresolvedConstructorSymbolMap (testId "C") (koreSort "S") [])
        , smtForSymbolIs "C" "|HB_C|"
        ]
    , testsForModule "Definition with complex constructor-based sorts"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` sortDeclaration "T"
            `with`
                (symbolDeclaration "C" "S" [] `with` [functional, constructor])
            `with`
                (symbolDeclaration "D" "S" ["T"]
                    `with` [functional, constructor]
                )
            `with` constructorAxiom "S" [("C", []), ("D", ["T"])]
        )
        [ inDeclarations
            (unresolvedConstructorSymbolMap (testId "C") (koreSort "S") [])
        , inDeclarations
            (unresolvedConstructorSymbolMap
                (testId "D")
                (koreSort "S")
                [koreSort "T"]
            )
        , smtForSymbolIs "C" "|HB_C|"
        , smtForSymbolIs "D" "|HB_D|"
        ]
    , testsForModule "Declares smtlib without name encoding"
        (indexModule $ emptyModule "m"
            `with` sortDeclaration "S"
            `with` sortDeclaration "T"
            `with` (symbolDeclaration "C" "S" ["T"] `with` smtlib "c")
        )
        [ inDeclarations
            (unresolvedSmtlibSymbolMap
                (testId "C") "c" [koreSort "T"] (koreSort "S")
            )
        , smtForSymbolIs "C" "c"
        ]
    , testsForModule "Declares smthook"
        (indexModule $ emptyModule "m"
            `with` (sortDeclaration "Integer" `with` hook Int.sort)
            `with`
                (symbolDeclaration "minus" "Integer" ["Integer"]
                    `with` smthook "-"
                )
        )
        [ inDeclarations
            (unresolvedSmthookSymbolMap
                (testId "minus") "-" (koreSort "Integer") [ koreSort "Integer"]
            )
        , smtForSymbolIs "minus" "-"
        ]
    ]
  where
    inDeclarations
        ::  ( HasCallStack
            , Diff (AST.Symbol sort name)
            )
        => (Kore.Id, AST.Symbol sort name)
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
    Helpers.testsForModule name buildRepresentations
